-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_convergence_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:43:10.162186+00:00
-- url     : https://prove2.me/submissions/8d855cf9-0a33-429a-afac-e88feddddf42

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_HotRepresentative_ae_good_q80

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

protected theorem add (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p) :
    UnifIntegrable (f + g) p μ :=
  ⟨hf.1.add hg.1 hp hf.2 hg.2, fun i => (hf.2 i).add (hg.2 i)⟩

protected theorem sub (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p) :
    UnifIntegrable (f - g) p μ :=
  ⟨hf.1.sub hg.1 hp hf.2 hg.2, fun i => (hf.2 i).sub (hg.2 i)⟩

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

protected theorem comp {ι' : Type*} (g : ι' → ι) (hf : UnifIntegrable f p μ) :
    UnifIntegrable (f ∘ g) p μ :=
  ⟨fun _ hε => (hf.1 hε).imp fun _ ⟨hδ, h⟩ => ⟨hδ, fun i s => h (g i) s⟩, fun i => hf.2 (g i)⟩

end UnifIntegrable

theorem tendsto_Lp_finite_of_tendstoInMeasure [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : TendstoInMeasure μ f atTop g) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure hp hp' hf hg hui.1 hfg

/-! ### `UniformIntegrable` -/

namespace UniformIntegrable

protected theorem unifIntegrable (hf : UniformIntegrable f p μ) : UnifIntegrable f p μ :=
  hf.1

protected theorem memLp (hf : UniformIntegrable f p μ) (i : ι) : MemLp (f i) p μ :=
  (uniformIntegrable_iff_mathlib.1 hf).memLp i

theorem toMathlib (hf : UniformIntegrable f p μ) : MeasureTheory.UniformIntegrable f p μ :=
  uniformIntegrable_iff_mathlib.1 hf

theorem ae_eq (hf : UniformIntegrable f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UniformIntegrable g p μ :=
  uniformIntegrable_iff_mathlib.2 (hf.toMathlib.ae_eq hfg)

lemma memLp_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f p μ) (htends : TendstoInMeasure μ f u g) : MemLp g p μ :=
  hUI.toMathlib.memLp_of_tendstoInMeasure htends

lemma integrable_of_tendstoInMeasure {κ : Type*} {u : Filter κ} [NeBot u]
    [IsCountablyGenerated u] {f : κ → α → β} {g : α → β}
    (hUI : UniformIntegrable f 1 μ) (htends : TendstoInMeasure μ f u g) : Integrable g μ :=
  hUI.toMathlib.integrable_of_tendstoInMeasure htends

end UniformIntegrable


/-! ### `UnifTight` -/

namespace UnifTight

theorem toMathlib (hf : UnifTight f p μ) : MeasureTheory.UnifTight f p μ :=
  unifTight_iff_mathlib.1 hf

protected theorem exists_measurableSet_indicator (hf : UnifTight f p μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε :=
  hf.toMathlib.exists_measurableSet_indicator hε

protected theorem comp {ι' : Type*} (g : ι' → ι) (hf : UnifTight f p μ) :
    UnifTight (f ∘ g) p μ :=
  fun ε hε => (hf ε hε).imp fun _ ⟨hμ, h⟩ => ⟨hμ, fun i => h (g i)⟩

end UnifTight

end OAI

end UnifIntegrableCompat
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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Uniform transverse disk bounds

This proves the translated disk estimate `ker:disk-singularity` from Section 3.
The singular contribution is split at distance `R` from the origin. Inside,
polar integration is explicit; outside, the singularity is at most `R⁻ᑫ`.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.TransverseDisk

theorem disk_volume_real (a : Transverse) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (ball a R) = Real.pi * R ^ 2 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

end BoltzmannNonuniqueness.TransverseDisk

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

theorem scale_pow (s₀ η : ℝ) (j p : ℕ) :
    scale s₀ η j ^ p = s₀ ^ p * Real.exp (-((p : ℝ) * η) * j) := by
  rw [scale, mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

/-- Polynomial factors in the index remain summable against every positive power of the
geometric scale. This is used with `p = 2` and index powers zero and one below. -/
theorem summable_scale_pow_mul_nat_pow (s₀ : ℝ) {η : ℝ} (hη : 0 < η)
    (p k : ℕ) (hp : 0 < p) :
    Summable (fun j : ℕ => scale s₀ η j ^ p * (j : ℝ) ^ k) := by
  have hrate : 0 < (p : ℝ) * η := mul_pos (by exact_mod_cast hp) hη
  have h := (Real.summable_pow_mul_exp_neg_nat_mul k hrate).mul_left (s₀ ^ p)
  apply h.congr
  intro j
  rw [scale_pow]
  ring

theorem summable_scale_pow (s₀ : ℝ) {η : ℝ} (hη : 0 < η)
    (p : ℕ) (hp : 0 < p) : Summable (fun j : ℕ => scale s₀ η j ^ p) := by
  simpa only [pow_zero, mul_one] using summable_scale_pow_mul_nat_pow s₀ hη p 0 hp

theorem summable_scale_sq (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun j : ℕ => scale s₀ η j ^ 2) :=
  summable_scale_pow s₀ hη 2 (by norm_num)

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

theorem mask_subset_ball {η s : ℝ} (hη : 0 ≤ η) (a : Bool) :
    mask η s a ⊆ ball 0 (Real.exp η * s) := by
  intro y hy
  have hc : 0 ≤ gapCoefficient η := by
    unfold gapCoefficient
    have := Real.one_le_exp hη
    positivity
  have h := hy.1.2
  change ‖y‖ < Real.exp η * s - gapCoefficient η * s ^ 2 at h
  rw [mem_ball, dist_zero_right]
  exact h.trans_le (sub_le_self _ (mul_nonneg hc (sq_nonneg s)))

theorem mask_finite {η s : ℝ} (hη : 0 ≤ η) (a : Bool) : volume (mask η s a) < ∞ :=
  (measure_mono (mask_subset_ball (s := s) hη a)).trans_lt (measure_ball_lt_top ..)

theorem mask_area_le {η s : ℝ} (hη : 0 ≤ η) (hs : 0 ≤ s) (a : Bool) :
    volume.real (mask η s a) ≤ Real.pi * (Real.exp η * s) ^ 2 := by
  have h := measureReal_mono (μ := (volume : Measure Transverse)) (mask_subset_ball (s := s) hη a)
  rw [TransverseDisk.disk_volume_real 0 (mul_nonneg (Real.exp_pos η).le hs)] at h
  exact h

theorem mask_area_uniform {η s : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hs : 0 ≤ s) (a : Bool) : volume.real (mask η s a) ≤ 4 * Real.pi * s ^ 2 := by
  apply (mask_area_le hη hs a).trans
  have he : Real.exp η ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hηmax
  have hp := mul_le_mul_of_nonneg_right he hs
  have hsq : (Real.exp η * s) ^ 2 ≤ (2 * s) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hp
  nlinarith [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]

theorem indicator_integrable {η s : ℝ} (hη : 0 ≤ η) (a : Bool) :
    Integrable ((mask η s a).indicator (fun _ => (1 : ℝ))) :=
  integrable_indicator_iff (measurableSet_mask η s a) |>.mpr
    (integrableOn_const (mask_finite hη a).ne)

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

theorem J_integrable : Integrable J := bump.integrable_normed

theorem J_integral : ∫ v, J v = 1 := bump.integral_normed

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

section

/-! # Mass, support and integrability of translated thermal profiles -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetThermalKernel

namespace BoltzmannNonuniqueness.JetThermalLaw

theorem integrable_scaled {f : Velocity → ℝ} (hf : Integrable f) {d : ℝ}
    (hd : 0 < d) (a : Velocity) : Integrable (scaled d a f) :=
  ((hf.comp_smul (inv_ne_zero hd.ne')).comp_sub_right a).const_mul _

theorem integral_scaled (f : Velocity → ℝ) {d : ℝ} (hd : 0 < d) (a : Velocity) :
    (∫ v, scaled d a f v) = ∫ v, f v := by
  unfold scaled
  rw [integral_const_mul]
  change (d ^ 3)⁻¹ * (∫ v, (fun w => f (d⁻¹ • w)) (v - a)) = _
  rw [integral_sub_right_eq_self (fun w => f (d⁻¹ • w)) a,
    Measure.integral_comp_inv_smul_of_nonneg volume f hd.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  field_simp

theorem density_nonneg {d : ℝ} (hd : 0 ≤ d) (a v : Velocity) : 0 ≤ density d a v :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hd _)) (J_nonneg _)

theorem density_integrable {d : ℝ} (hd : 0 < d) (a : Velocity) : Integrable (density d a) :=
  integrable_scaled J_integrable hd a

theorem density_mass {d : ℝ} (hd : 0 < d) (a : Velocity) : ∫ v, density d a v = 1 := by
  rw [density, integral_scaled J hd a, J_integral]

end BoltzmannNonuniqueness.JetThermalLaw

end

end

section

/-! # The integrable hyperbolic axial weight of the cold datum -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetAxialWeight

theorem scaled_derivative (γ s x : ℝ) :
    HasDerivAt (fun z => Real.tanh (γ * z / s)) ((γ / s) * S (γ * x / s)) x := by
  have h := (tanh_derivative (γ * x / s)).comp x
    (((hasDerivAt_id x).const_mul γ).div_const s)
  have he : S (γ * x / s) * (γ * 1 / s) = (γ / s) * S (γ * x / s) := by ring
  rw [he] at h
  exact h

theorem scaled_intervalIntegral {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (a b : ℝ) :
    (∫ z in a..b, S (γ * z / s)) =
      (s / γ) * (Real.tanh (γ * b / s) - Real.tanh (γ * a / s)) := by
  have hc : Continuous (fun z : ℝ => S (γ * z / s)) :=
    continuous_S.comp ((continuous_const.mul continuous_id).div_const s)
  have hd (x : ℝ) : HasDerivAt (fun z => (s / γ) * Real.tanh (γ * z / s))
      (S (γ * x / s)) x := by
    have h := (scaled_derivative γ s x).const_mul (s / γ)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable a b)]
  ring

theorem scaled_intervalIntegral_le {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (a b : ℝ) :
    (∫ z in a..b, S (γ * z / s)) ≤ 2 * s / γ := by
  rw [scaled_intervalIntegral hγ hs]
  have hb : Real.tanh (γ * b / s) - Real.tanh (γ * a / s) ≤ 2 := by
    linarith [Real.tanh_lt_one (γ * b / s), Real.neg_one_lt_tanh (γ * a / s)]
  have h := mul_le_mul_of_nonneg_left hb (div_pos hs hγ).le
  exact h.trans_eq (by ring)

end BoltzmannNonuniqueness.JetAxialWeight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_WeightAlgebra
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weight transfer on a collision plane

The exact Gaussian identity and polynomial transfer turn the normalized
gain weight into the tilted cold measure used in `ker:tilted-kernel`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.VelocityWeight

theorem tiltConstant_pos : 0 < tiltConstant := by unfold tiltConstant; positivity

theorem polynomial_le_gaussian (p : Velocity) :
    (1 + ‖p‖ ^ 2) ^ (50 : ℕ) ≤ tiltConstant * Real.exp (‖p‖ ^ 2) := by
  have hf : 0 < (Nat.factorial 50 : ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (1 + ‖p‖ ^ 2) (by positivity) 50)
  calc
    _ ≤ Real.exp (1 + ‖p‖ ^ 2) * (Nat.factorial 50 : ℝ) := h
    _ = _ := by unfold tiltConstant; rw [Real.exp_add]; ring

end BoltzmannNonuniqueness.VelocityWeight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_GainNonnegative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positivity and domination for the original gain integral -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.GainOrder

theorem integrand_nonneg {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (p : Velocity × Sphere) : 0 ≤ integrand f v p :=
  mul_nonneg (mul_nonneg (collisionKernel_nonneg _ _ _) (hf _)) (hf _)

theorem integrand_mono {f g : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w)
    (v : Velocity) (p : Velocity × Sphere) : integrand f v p ≤ integrand g v p := by
  unfold integrand
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hfg _) (collisionKernel_nonneg _ _ _))
    (hfg _) (hf _) (mul_nonneg (collisionKernel_nonneg _ _ _) ((hf _).trans (hfg _)))

theorem integrand_measurable {f : Velocity → ℝ} (hf : Measurable f) (v : Velocity) :
    Measurable (integrand f v) := by
  have hleft : Measurable (fun p : Velocity × Sphere => scatterLeft v p.1 p.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hright : Measurable (fun p : Velocity × Sphere => scatterRight v p.1 p.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : Velocity × Sphere => collisionKernel v p.1 p.2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hk.mul (hf.comp hleft)).mul (hf.comp hright)

theorem integrable_of_le {f g : Velocity → ℝ} (hm : Measurable f)
    (hf : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w) (v : Velocity)
    (hg : Integrable (integrand g v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand f v) ((volume : Measure Velocity).prod sphereArea) := by
  apply hg.mono' (integrand_measurable hm v).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hf v p)]
  exact integrand_mono hf hfg v p

theorem gain_mono {f g : Velocity → ℝ} (hm : Measurable f)
    (hf : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w) (v : Velocity) (x : Position)
    (hg : Integrable (integrand g v) ((volume : Measure Velocity).prod sphereArea)) :
    gain (fun p => f p.2) x v ≤ gain (fun p => g p.2) x v :=
  integral_mono (integrable_of_le hm hf hfg v hg) hg (integrand_mono hf hfg v)

theorem gain_const_mul (c : ℝ) (f : Velocity → ℝ) (v : Velocity) (x : Position) :
    gain (fun p => c * f p.2) x v = c ^ 2 * gain (fun p => f p.2) x v := by
  unfold gain
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  ring

theorem integrable_const_mul (c : ℝ) {f : Velocity → ℝ} (v : Velocity)
    (hf : Integrable (integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand (fun w => c * f w) v) ((volume : Measure Velocity).prod sphereArea) := by
  convert hf.const_mul (c ^ 2) using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  unfold integrand
  ring

end BoltzmannNonuniqueness.GainOrder

end

end

section

/-! # Conversion from the nonnegative Carleman gain to the real collision operator -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.GainNonnegative

theorem self_eq_lintegral {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (v : Velocity) :
    nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v =
      ∫⁻ p, ENNReal.ofReal (GainOrder.integrand f v p)
        ∂((volume : Measure Velocity).prod sphereArea) := by
  unfold nonnegativeGain gainPairMeasure
  apply lintegral_congr
  intro p
  have hp := mul_nonneg (hf (scatterLeft v p.1 p.2)) (hf (scatterRight v p.1 p.2))
  have he : ENNReal.ofReal (collisionKernel v p.1 p.2) / 2 =
      ENNReal.ofReal (collisionKernel v p.1 p.2 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← ENNReal.ofReal_mul (hf (scatterLeft v p.1 p.2)),
    ← ENNReal.ofReal_add hp hp, he,
    ← ENNReal.ofReal_mul (div_nonneg (collisionKernel_nonneg _ _ _) (by norm_num))]
  congr 1
  unfold GainOrder.integrand
  ring

theorem integrable_of_bound {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    {B : ℝ} (v : Velocity)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v ≤
      ENNReal.ofReal B) :
    Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea) := by
  refine ⟨(GainOrder.integrand_measurable hm v).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (GainOrder.integrand_nonneg hf v)),
    ← self_eq_lintegral hf v]
  exact hb.trans_lt ENNReal.ofReal_lt_top

theorem gain_le_of_bound {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    {B : ℝ} (hB : 0 ≤ B) (v : Velocity) (x : Position)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v ≤
      ENNReal.ofReal B) : gain (fun p => f p.2) x v ≤ B := by
  have hi := integrable_of_bound hm hf v hb
  have he : gain (fun p => f p.2) x v =
      (nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v).toReal := by
    rw [self_eq_lintegral hf]
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (GainOrder.integrand_nonneg hf v)) hi.aestronglyMeasurable
  rw [he]
  simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end BoltzmannNonuniqueness.GainNonnegative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

section

/-! # The relative-speed cutoff used in the finite approximations -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCutoff

theorem rate_nonneg (b : ℝ) (v w : Velocity) : 0 ≤ rate b v w := by
  unfold rate
  split_ifs <;> positivity

theorem rate_le {b : ℝ} (hb : 0 ≤ b) (v w : Velocity) : rate b v w ≤ b := by
  unfold rate
  split_ifs with h
  · exact h.le
  · exact hb

theorem measurable_rate (b : ℝ) (v : Velocity) : Measurable (rate b v) := by
  unfold rate
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) measurable_const

theorem integrable_frequency {b : ℝ} (hb : 0 ≤ b) {f : Velocity → ℝ} (hf : Integrable f)
    (v : Velocity) : Integrable (fun w => rate b v w * f w) := by
  apply (hf.norm.const_mul b).mono' ((measurable_rate b v).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with w
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rate_nonneg b v w)]
  exact mul_le_mul_of_nonneg_right (rate_le hb v w) (norm_nonneg _)

theorem abs_frequency_le {b : ℝ} (hb : 0 ≤ b) {f : Velocity → ℝ} (hf : Integrable f)
    (v : Velocity) : |frequency b f v| ≤ 2 * Real.pi * b * ∫ w, |f w| := by
  have hi := integrable_frequency hb hf v
  have hm : Integrable (fun w => b * |f w|) := by simpa only [Real.norm_eq_abs] using hf.norm.const_mul b
  have hpoint (w : Velocity) : |rate b v w * f w| ≤ b * |f w| := by
    rw [abs_mul, abs_of_nonneg (rate_nonneg b v w)]
    exact mul_le_mul_of_nonneg_right (rate_le hb v w) (abs_nonneg _)
  calc
    _ = 2 * Real.pi * |∫ w, rate b v w * f w| := by
      rw [frequency, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    _ ≤ 2 * Real.pi * ∫ w, |rate b v w * f w| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by positivity)
    _ ≤ 2 * Real.pi * ∫ w, b * |f w| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono (by simpa only [Real.norm_eq_abs] using hi.norm) hm hpoint
    _ = _ := by rw [integral_const_mul]; ring

theorem kernel_nonneg (b : ℝ) (v w : Velocity) (ω : Sphere) : 0 ≤ kernel b v w ω := by
  unfold kernel
  split_ifs
  · exact collisionKernel_nonneg _ _ _
  · exact le_rfl

theorem kernel_le (b : ℝ) (v w : Velocity) (ω : Sphere) : kernel b v w ω ≤ collisionKernel v w ω := by
  unfold kernel
  split_ifs
  · exact le_rfl
  · exact collisionKernel_nonneg _ _ _

theorem integrand_le (b : ℝ) {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (p : Velocity × Sphere) : integrand b f v p ≤ GainOrder.integrand f v p := by
  unfold integrand GainOrder.integrand
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (kernel_le b v p.1 p.2) (hf _)) (hf _)

theorem integrable_gain (b : ℝ) {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (hi : Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand b f v) ((volume : Measure Velocity).prod sphereArea) := by
  have he (p : Velocity × Sphere) : integrand b f v p =
      if ‖v - p.1‖ < b then GainOrder.integrand f v p else 0 := by
    unfold integrand kernel GainOrder.integrand
    split_ifs <;> simp only [zero_mul]
  change Integrable (fun p => integrand b f v p) _
  simp_rw [he]
  apply hi.mono'
  · exact ((GainOrder.integrand_measurable hm v).ite
      (measurableSet_lt (by fun_prop) measurable_const) measurable_const).aestronglyMeasurable
  · filter_upwards [] with p
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (GainOrder.integrand_nonneg hf v p)]
    · simpa only [norm_zero] using GainOrder.integrand_nonneg hf v p

theorem gain_le (b : ℝ) {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (x : Position)
    (hi : Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    gain b f v ≤ BoltzmannNonuniqueness.gain (fun p => f p.2) x v :=
  integral_mono (integrable_gain b hm hf v hi) hi (integrand_le b hf v)

end BoltzmannNonuniqueness.CollisionCutoff

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticDensityMeasurable
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Collision representative invariance with space and time parameters -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.KineticCollisionNullSets

variable {X : Type*} [MeasurableSpace X]

theorem measurable_gain {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (gain b f) := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hL : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) => f (left p)) := by
    apply hf.comp
    unfold left scatterLeft normalComponent
    fun_prop
  have hR : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) => f (right p)) := by
    apply hf.comp
    unfold right scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) =>
      CollisionCutoff.kernel b p.1.2 p.2.1 p.2.2) := by
    unfold CollisionCutoff.kernel
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · unfold collisionKernel normalComponent
      fun_prop
    · exact measurable_const
  exact ((hk.mul hL).mul hR).stronglyMeasurable.integral_prod_right.measurable

theorem measurable_frequency {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (frequency b f) := by
  have hk : Measurable (fun p : (X × Velocity) × Velocity =>
      CollisionCutoff.rate b p.1.2 p.2) := by
    unfold CollisionCutoff.rate
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (by fun_prop) measurable_const
  have hm : Measurable (fun p : (X × Velocity) × Velocity => f (p.1.1, p.2)) := by
    exact hf.comp (measurable_fst.fst.prodMk measurable_snd)
  exact measurable_const.mul (hk.mul hm).stronglyMeasurable.integral_prod_right.measurable

end BoltzmannNonuniqueness.KineticCollisionNullSets

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotGainReduction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Algebraic reduction of the quadratic hot gain

Symmetry allows the output polynomial weight to be assigned to either
incoming velocity. The resulting mixed gain has only one polynomial factor,
while its two Gaussian factors cancel by collision energy conservation.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotWeight

theorem polynomial_pos (v : Velocity) : 0 < polynomial v := by
  unfold polynomial
  positivity

theorem H_mul_polynomial (q : ℝ) (v : Velocity) : H q v * polynomial v = G q v := by
  unfold H polynomial G
  change Real.exp (-‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) * W q v *
    (1 + ‖v‖ ^ 2) ^ (50 : ℕ) = _
  rw [show (-50 : ℝ) = -(50 : ℕ) by norm_num,
    Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hp : (1 + ‖v‖ ^ 2) ^ (50 : ℕ) ≠ 0 := by positivity
  field_simp

end BoltzmannNonuniqueness.HotWeight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotQuadraticGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The quadratic hot-gain bound

The geometric shell estimates and their summation transfer through the
Carleman identity to the original hard-sphere collision variables.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.HotMixedGain

namespace BoltzmannNonuniqueness.HotApplication

theorem realBound_pos (q : ℝ) : 0 < realBound q := by
  unfold realBound
  positivity

end BoltzmannNonuniqueness.HotApplication

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

theorem axialAmplitude_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (γ z : ℝ) :
    0 ≤ axialAmplitude K γ s z := by
  apply indicator_nonneg
  intro z _
  exact mul_nonneg (div_nonneg hK hs) (S_pos _).le

theorem spatial_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (η γ : ℝ) (a : Bool) (x : Space) :
    0 ≤ spatial η K γ s a x :=
  mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
    (axialAmplitude_nonneg hK hs γ _)

theorem density_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ : ℝ) (a : Bool) (p : Phase) : 0 ≤ density η K α γ s d a p :=
  mul_nonneg (spatial_nonneg hK hs η γ a _)
    (JetThermalLaw.density_nonneg hd _ _)

theorem axialAmplitude_integrable (K γ s : ℝ) : Integrable (axialAmplitude K γ s) := by
  apply integrable_indicator_iff measurableSet_Ioo |>.mpr
  exact (((continuous_const.mul (continuous_S.comp
    ((continuous_const.mul continuous_id).div_const s))).integrableOn_Icc).mono_set Ioo_subset_Icc_self)

theorem spatial_integrable {η : ℝ} (hη : 0 ≤ η) (K γ s : ℝ) (a : Bool) :
    Integrable (spatial η K γ s a) spaceVolume :=
  (indicator_integrable hη a).mul_prod (axialAmplitude_integrable K γ s)

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

theorem density_velocity_integral {d : ℝ} (hd : 0 < d)
    (η K α γ s : ℝ) (a : Bool) (x : Space) :
    (∫ v, density η K α γ s d a (x, v)) = spatial η K γ s a x := by
  simp only [density, integral_const_mul, JetThermalLaw.density_mass hd, mul_one]

theorem density_integrable {η K s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hs : 0 ≤ s) (hd : 0 < d) (α γ : ℝ) (a : Bool) :
    Integrable (density η K α γ s d a) (spaceVolume.prod volume) := by
  apply (integrable_prod_iff (measurable_density η K α γ s d a).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    exact (JetThermalLaw.density_integrable hd (center α γ s a x.2)).const_mul
      (spatial η K γ s a x)
  · have he : (fun x : Space => ∫ v, ‖density η K α γ s d a (x, v)‖) =
        spatial η K γ s a := by
      funext x
      simp_rw [Real.norm_of_nonneg (density_nonneg hK hs hd.le η α γ a _)]
      exact density_velocity_integral hd η K α γ s a x
    rw [he]
    exact spatial_integrable hη K γ s a

theorem density_mass_eq {η K s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hs : 0 ≤ s) (hd : 0 < d) (α γ : ℝ) (a : Bool) :
    (∫ p, density η K α γ s d a p ∂spaceVolume.prod volume) =
      volume.real (mask η s a) * ((K / s) *
        ∫ z in Ioo (-(1 / 8 : ℝ)) (1 / 8), S (γ * z / s)) := by
  rw [integral_prod _ (density_integrable hη hK hs hd α γ a)]
  simp_rw [density_velocity_integral hd]
  unfold spatial spaceVolume
  rw [integral_prod_mul, integral_indicator (measurableSet_mask η s a), setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  unfold axialAmplitude
  rw [integral_indicator measurableSet_Ioo, integral_const_mul]

theorem density_mass_bound {η K γ s d : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    (∫ p, density η K α γ s d a p ∂spaceVolume.prod volume) ≤
      (8 * Real.pi * K / γ) * s ^ 2 := by
  rw [density_mass_eq hη hK hs.le hd]
  have hz : (∫ z in Ioo (-(1 / 8 : ℝ)) (1 / 8), S (γ * z / s)) ≤ 2 * s / γ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num :
      -(1 / 8 : ℝ) ≤ 1 / 8)]
    exact scaled_intervalIntegral_le hγ hs _ _
  have hm := mul_le_mul_of_nonneg_left hz (div_nonneg hK hs.le)
  have ha := mask_area_uniform hη hηmax hs.le a
  calc
    _ ≤ volume.real (mask η s a) * ((K / s) * (2 * s / γ)) :=
      mul_le_mul_of_nonneg_left hm measureReal_nonneg
    _ ≤ (4 * Real.pi * s ^ 2) * ((K / s) * (2 * s / γ)) :=
      mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := by field_simp <;> ring

end BoltzmannNonuniqueness.JetPrototype

end

end

section

/-! # Velocity support and spatial confinement of the free cold cores -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetSupport

theorem initial_spatial_support (η K α γ s d : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    p.1.1 ∈ mask η s a ∧ |p.1.2| < 1 / 8 := by
  have hsp : spatial η K γ s a p.1 ≠ 0 := left_ne_zero_of_mul hp
  have hm : (mask η s a).indicator (fun _ => (1 : ℝ)) p.1.1 ≠ 0 := left_ne_zero_of_mul hsp
  have hz : axialAmplitude K γ s p.1.2 ≠ 0 := right_ne_zero_of_mul hsp
  have hy : p.1.1 ∈ mask η s a := by
    by_contra h
    exact hm (indicator_of_notMem h _)
  have hz' : p.1.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8) := by
    by_contra h
    exact hz (indicator_of_notMem h _)
  exact ⟨hy, abs_lt.mpr hz'⟩

end BoltzmannNonuniqueness.JetSupport

end

end

section

/-! # Gaussian decay of a cold barrier away from its spatial core -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetGaussianEscape

theorem gaussian_le_hot (q : ℝ) (v : Velocity) :
    Real.exp (-2 * ‖v‖ ^ 2) ≤ tiltConstant * H q v := by
  have hp := polynomial_le_gaussian v
  have hw : 1 ≤ W q v := by unfold W; linarith [singularity_nonneg q (transverse v)]
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-2 * ‖v‖ ^ 2))
  have hexp : Real.exp (-2 * ‖v‖ ^ 2) * Real.exp (‖v‖ ^ 2) = Real.exp (-‖v‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : Real.exp (-2 * ‖v‖ ^ 2) * HotWeight.polynomial v ≤
      tiltConstant * HotWeight.G q v := by
    calc
      _ ≤ tiltConstant * Real.exp (-‖v‖ ^ 2) := by
        change Real.exp (-2 * ‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (50 : ℕ) ≤ _
        calc
          _ ≤ Real.exp (-2 * ‖v‖ ^ 2) * (tiltConstant * Real.exp (‖v‖ ^ 2)) := hm
          _ = _ := by rw [mul_left_comm, hexp]
      _ ≤ _ := by
        unfold HotWeight.G
        simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hw
          (mul_nonneg tiltConstant_pos.le (Real.exp_nonneg (-‖v‖ ^ 2)))
  rw [← HotWeight.H_mul_polynomial] at hprod
  exact (mul_le_mul_iff_of_pos_right (HotWeight.polynomial_pos v)).mp (by
    simpa only [mul_assoc] using hprod)

end BoltzmannNonuniqueness.JetGaussianEscape

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusChart
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.MassTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A centered fundamental cube for the periodic spatial variable -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusChart

theorem coordinate_measurePreserving : MeasurePreserving coordinate volume (volume.restrict interval) := by
  have h := (measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
    (s := Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) measurableSet_Ioc).comp
    (AddCircle.measurePreserving_equivIoc (T := (1 : ℝ)) (a := -(1 / 2 : ℝ)))
  change MeasurePreserving (Subtype.val ∘ (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))))
    volume (volume.restrict interval)
  have he : Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) = interval := by norm_num [interval]
  rw [← he]
  exact h

theorem measurableSet_cube : MeasurableSet cube := by
  have he : cube = ⋂ i : Fin 3, {x : Velocity | x i ∈ interval} := by ext x; simp [cube]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_Ioc.preimage
    (show Measurable (fun x : Velocity => x i) from (PiLp.continuous_apply 2 _ i).measurable))

theorem representative_measurePreserving :
    MeasurePreserving representative volume (volume.restrict cube) := by
  have hp := measurePreserving_pi (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ : Fin 3 => (volume : Measure ℝ).restrict interval) (fun _ => coordinate_measurePreserving)
  have he := (PiLp.volume_preserving_toLp (ι := Fin 3)).restrict_preimage measurableSet_cube
  have hpre : WithLp.toLp 2 ⁻¹' cube = Set.univ.pi (fun _ : Fin 3 => interval) := by
    ext x
    simp [cube, Set.mem_pi, interval]
  rw [hpre] at he
  change MeasurePreserving (WithLp.toLp 2)
    ((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict (Set.univ.pi (fun _ => interval)))
    (volume.restrict cube) at he
  rw [Measure.restrict_pi_pi] at he
  exact he.comp hp

theorem representative_mem (x : Position) : representative x ∈ cube := by
  intro i
  have h := ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) (x i)).property
  change -(1 / 2 : ℝ) < coordinate (x i) ∧ coordinate (x i) ≤ 1 / 2
  constructor
  · exact h.1
  · change ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) (x i) : ℝ) ≤ 1 / 2
    linarith [h.2]

theorem projection_representative (x : Position) : torusProjection (representative x) = x := by
  funext i
  exact AddCircle.coe_equivIoc

theorem phase_measurePreserving : MeasurePreserving phaseRepresentative
    (volume : Measure Phase) ((volume : Measure (Velocity × Velocity)).restrict (cube ×ˢ univ)) := by
  change MeasurePreserving phaseRepresentative
    ((volume : Measure Position).prod (volume : Measure Velocity))
    (((volume : Measure Velocity).prod (volume : Measure Velocity)).restrict (cube ×ˢ univ))
  rw [← Measure.prod_restrict]
  have h := representative_measurePreserving.prod (MeasurePreserving.id (volume : Measure Velocity))
  simp only [Measure.restrict_univ]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

end BoltzmannNonuniqueness.TorusChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetPeriodicDatum
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integration of the nonnegative, disjoint cold-jet series -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetSeries

theorem summable_single_support {ι : Type*} {f : ι → ℝ}
    (hf : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) : Summable f := by
  classical
  by_cases h : ∃ i, f i ≠ 0
  · obtain ⟨i, hi⟩ := h
    exact summable_of_ne_finset_zero (s := {i}) (fun j hj => hf i j (by simpa [eq_comm] using hj) hi)
  · have he : f = 0 := by ext i; simpa using not_exists.mp h i
    rw [he]
    exact summable_zero

theorem integrable_nonnegative_series {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → ℝ}
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (f i) μ)
    (hn : ∀ i x, 0 ≤ f i x) (hs : ∀ x, Summable (fun i => f i x))
    (hI : Summable (fun i => ∫ x, f i x ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun x => tsum_nonneg (fun i => hn i x)))).mpr
  have he : (∫⁻ x, ENNReal.ofReal (∑' i, f i x) ∂μ) =
      ∑' i, ENNReal.ofReal (∫ x, f i x ∂μ) := by
    simp_rw [ENNReal.ofReal_tsum_of_nonneg (fun i => hn i _) (hs _)]
    rw [lintegral_tsum (fun i => (hm i).ennreal_ofReal.aemeasurable)]
    congr 1
    funext i
    exact (ofReal_integral_eq_lintegral_ofReal (hi i)
      (Filter.Eventually.of_forall (hn i))).symm
  rw [he]
  exact hI.tsum_ofReal_lt_top

end BoltzmannNonuniqueness.JetSeries

end

end

section

/-! # The full unperiodized cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetDatum

theorem term_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ : ℝ) (i : Index) (p : JetPrototype.Phase) : 0 ≤ term s₀ η K α γ d₀ i p :=
  density_nonneg hK (DatumBounds.scale_pos hs₀ _).le
    (mul_nonneg hd₀ (pow_nonneg (DatumBounds.scale_pos hs₀ _).le _)) η α γ i.2 p

theorem term_integrable {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η)
    (hK : 0 ≤ K) (hd₀ : 0 < d₀) (α γ : ℝ) (i : Index) :
    Integrable (term s₀ η K α γ d₀ i) (spaceVolume.prod volume) :=
  density_integrable hη hK (DatumBounds.scale_pos hs₀ _).le
    (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _)) α γ i.2

theorem term_measurable (s₀ η K α γ d₀ : ℝ) (i : Index) :
    Measurable (term s₀ η K α γ d₀ i) := measurable_density _ _ _ _ _ _ _

private theorem in_enlargement {s₀ η K α γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    {i : Index} {p : JetPrototype.Phase} (hp : term s₀ η K α γ d₀ i p ≠ 0) :
    PlaneChart.join p.1.1 p.1.2 ∈ JetLattice.spatialEnlargement s₀ η 0 (label i) := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.1 + 1)
  have hsp := JetSupport.initial_spatial_support η K α γ _ _ i.2 hp
  constructor
  · change transverse (PlaneChart.join p.1.1 p.1.2) - JetLattice.transverseShift 0 ∈
      enlargement η (jetScale s₀ η i.1) i.2
    have hz : JetLattice.transverseShift 0 = 0 := by ext k; simp [JetLattice.transverseShift]
    rw [PlaneChart.transverse_join, hz, sub_zero]
    exact Metric.mem_cthickening_of_dist_le p.1.1 p.1.1 _ _ hsp.1
      (by simpa [jetScale] using (enlargementWidth_pos hη hs).le)
  · simpa [label, JetLattice.axialShift, PlaneChart.axial_join] using
      (show |p.1.2| ≤ 1 / 8 + 2 * (0 : ℝ) + 1 / 16 by linarith [hsp.2])

theorem term_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase)
    (i j : Index) (hij : i ≠ j) (hi : term s₀ η K α γ d₀ i p ≠ 0) :
    term s₀ η K α γ d₀ j p = 0 := by
  by_contra hj
  have he := JetLattice.common_point_label hs₀ hsmax hη hηmax (by norm_num : (0 : ℝ) ≤ 1 / 32)
    (in_enlargement hs₀ hη hi) (in_enlargement hs₀ hη hj)
  apply hij
  exact Prod.ext (congrArg JetLattice.Label.annulus he) (congrArg JetLattice.Label.positive he)

theorem term_summable {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    Summable (fun i => term s₀ η K α γ d₀ i p) :=
  JetSeries.summable_single_support (term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p)

theorem summable_bool_extension {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (hs : Summable f) :
    Summable (fun i : Index => f i.1) := by
  apply (summable_prod_of_nonneg (fun i => hf i.1)).mpr
  constructor
  · intro j
    exact summable_of_hasFiniteSupport (Set.toFinite _)
  · simpa only [tsum_fintype, Fintype.sum_bool] using hs.add hs

theorem mass_summable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) :
    Summable (fun i : Index => ∫ p, term s₀ η K α γ d₀ i p ∂spaceVolume.prod volume) := by
  have hs : Summable (fun j => (8 * Real.pi * K / γ) * jetScale s₀ η j ^ 2) := by
    exact ((summable_nat_add_iff 1).mpr (DatumBounds.summable_scale_sq s₀ hη)).mul_left _
  apply Summable.of_nonneg_of_le
    (fun i => integral_nonneg (term_nonneg hs₀ hK hd₀.le η α γ i))
    (fun i => density_mass_bound hη.le hηmax hK hγ (DatumBounds.scale_pos hs₀ _)
      (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _)) α i.2)
    (summable_bool_extension (fun j => by positivity) hs)

theorem datum_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) : Integrable (datum s₀ η K α γ d₀) (spaceVolume.prod volume) :=
  JetSeries.integrable_nonnegative_series (term_measurable s₀ η K α γ d₀)
    (term_integrable hs₀ hη.le hK hd₀ α γ) (term_nonneg hs₀ hK hd₀.le η α γ)
    (term_summable hs₀ hsmax hη hηmax K α γ d₀) (mass_summable hs₀ hη hηmax hK hγ hd₀ α)

end BoltzmannNonuniqueness.JetDatum

end

end

section

/-! # Mass, energy, and entropy of the full cold datum -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetDatum

namespace BoltzmannNonuniqueness.JetDatumMoments

theorem datum_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ : ℝ) (p : JetPrototype.Phase) : 0 ≤ datum s₀ η K α γ d₀ p :=
  tsum_nonneg (fun i => term_nonneg hs₀ hK hd₀ η α γ i p)

end BoltzmannNonuniqueness.JetDatumMoments

end

end

section

/-! # Pointwise stabilization of the annular truncations -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetDatum

namespace BoltzmannNonuniqueness.JetTruncation

theorem truncated_measurable (s₀ η K α γ d₀ : ℝ) (N : ℕ) :
    Measurable (truncated s₀ η K α γ d₀ N) := by
  apply Measurable.tsum
  intro i
  by_cases hi : i.1 < N
  · simpa only [ite_eq_left hi] using term_measurable s₀ η K α γ d₀ i
  · simp only [ite_eq_right hi]
    exact measurable_const

theorem truncated_at_nonzero {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (N : ℕ)
    (p : JetPrototype.Phase) {i : Index} (hi : term s₀ η K α γ d₀ i p ≠ 0) :
    truncated s₀ η K α γ d₀ N p = if i.1 < N then datum s₀ η K α γ d₀ p else 0 := by
  have hz : ∀ j, j ≠ i → term s₀ η K α γ d₀ j p = 0 :=
    fun j hj => term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p i j hj.symm hi
  have hd : datum s₀ η K α γ d₀ p = term s₀ η K α γ d₀ i p := tsum_eq_single i hz
  unfold truncated
  rw [tsum_eq_single i]
  · rw [hd]
  · intro j hj
    simp only [hz j hj, ite_self]

theorem truncated_eq_or_zero {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (N : ℕ)
    (p : JetPrototype.Phase) :
    truncated s₀ η K α γ d₀ N p = datum s₀ η K α γ d₀ p ∨
      truncated s₀ η K α γ d₀ N p = 0 := by
  by_cases h : ∃ i, term s₀ η K α γ d₀ i p ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [truncated_at_nonzero hs₀ hsmax hη hηmax K α γ d₀ N p hi]
    split_ifs <;> simp
  · have hz : ∀ i, term s₀ η K α γ d₀ i p = 0 := fun i => not_ne_iff.mp (not_exists.mp h i)
    right
    simp only [truncated, hz, ite_self, tsum_zero]

end BoltzmannNonuniqueness.JetTruncation

end

end

section

/-! # The free cold core in Eulerian coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem flight_add (t r : ℝ) (p : JetPrototype.Phase) :
    flight t (flight r p) = flight (t + r) p := by
  apply Prod.ext
  · apply Prod.ext
    · dsimp only [flight]
      module
    · dsimp only [flight]
      ring
  · rfl

@[simp] theorem flight_neg (t : ℝ) (p : JetPrototype.Phase) : flight t (flight (-t) p) = p := by
  rw [flight_add, add_neg_cancel, flight_zero]

@[simp] theorem neg_flight (t : ℝ) (p : JetPrototype.Phase) : flight (-t) (flight t p) = p := by
  rw [flight_add, neg_add_cancel, flight_zero]

end BoltzmannNonuniqueness.JetFreeTransport

end

end

section

/-! # The cold datum on the actual unit spatial torus -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetPeriodicDatum

theorem integrable_pullback {f : JetPrototype.Phase → ℝ}
    (hf : Integrable f (spaceVolume.prod volume)) : Integrable (pullback f) := by
  have hl := phaseMap_measurePreserving.integrable_comp_of_integrable hf
  exact TorusChart.phase_measurePreserving.integrable_comp_of_integrable hl.restrict

end BoltzmannNonuniqueness.JetPeriodicDatum

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1Operations
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Published weak compactness input for the two kinetic measure spaces

N. Dunford and B. J. Pettis, *Linear operations on summable functions*,
Transactions of the AMS 47 (1940), 323–392, Theorem 3.2.1, p. 376,
DOI 10.1090/S0002-9947-1940-0002020-4.
Publisher: https://www.ams.org/journals/tran/1940-047-03/S0002-9947-1940-0002020-4/S0002-9947-1940-0002020-4.pdf

The hypothesis below is the sequential weak-compactness consequence for the
one- and two-velocity spaces used here. `UniformIntegrable` includes the common
L¹ bound; `UnifTight` supplies the necessary control at infinity. We require
both, including on the infinite velocity spaces. No Boltzmann equation,
nonlinear identification, or admissible solution is assumed by this input.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.nonneg {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) :
    ∀ᵐ x ∂μ, 0 ≤ g x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg h.2.1
  intro s hs _hfinite
  let ψ : X → ℝ := s.indicator (fun _ => 1)
  have hψ : Measurable ψ := measurable_const.indicator hs
  have hψB : ∃ C : ℝ, ∀ x, |ψ x| ≤ C := by
    refine ⟨1,fun x => ?_⟩
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  have ht := h.2.2 ψ hψ hψB
  have he (u : X → ℝ) : (∫ x, ψ x*u x ∂μ) = ∫ x in s, u x ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  simp_rw [he] at ht
  apply ge_of_tendsto ht
  exact Filter.Eventually.of_forall (fun n => integral_nonneg_of_ae (ae_restrict_of_ae (hf n)))

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

theorem WeakL1Converges.eq_of_strong {μ : Measure X} {f : ℕ → X → ℝ} {g A : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ) (hA : Integrable A μ)
    (hstrong : Tendsto (fun n => eLpNorm (fun x => f n x-A x) 1 μ) atTop (𝓝 0)) :
    A =ᵐ[μ] g := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq A g hA h.2.1
  intro s hs _hfinite
  let ψ : X → ℝ := s.indicator (fun _ => 1)
  have hψ : Measurable ψ := measurable_const.indicator hs
  have hB : ∃ C : ℝ, ∀ x, |ψ x| ≤ C := by
    refine ⟨1,fun x => ?_⟩
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  have hw := h.2.2 ψ hψ hB
  have he (u : X → ℝ) : (∫ x, ψ x*u x ∂μ) = ∫ x in s, u x ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  simp_rw [he] at hw
  have hsstrong : Tendsto (fun n => eLpNorm (fun x => f n x-A x) 1 (μ.restrict s))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hstrong
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have ha := tendsto_integral_of_L1' (hfi := hA.aestronglyMeasurable.restrict) A (Eventually.of_forall (fun n => (hf n).restrict)) hsstrong
  exact tendsto_nhds_unique ha hw

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

/-! # Linear operations on weak L¹ limits -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.sub {μ : Measure X} {f k : ℕ → X → ℝ} {g h : X → ℝ}
    (hf : WeakL1Converges μ f g) (hk : WeakL1Converges μ k h)
    (hfi : ∀ n, Integrable (f n) μ) (hki : ∀ n, Integrable (k n) μ) :
    WeakL1Converges μ (fun n x => f n x-k n x) (fun x => g x-h x) := by
  refine ⟨hf.1.sub hk.1,hf.2.1.sub hk.2.1,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have hm (u : X → ℝ) (hu : Integrable u μ) : Integrable (fun x => ψ x*u x) μ :=
    hu.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have he (u v : X → ℝ) (hu : Integrable u μ) (hv : Integrable v μ) :
      (∫ x, ψ x*(u x-v x) ∂μ) = (∫ x, ψ x*u x ∂μ)-(∫ x, ψ x*v x ∂μ) := by
    simp_rw [mul_sub]
    exact integral_sub (hm u hu) (hm v hv)
  simp_rw [he _ _ (hfi _) (hki _),he _ _ hf.2.1 hk.2.1]
  exact (hf.2.2 ψ hψ ⟨C,hC⟩).sub (hk.2.2 ψ hψ ⟨C,hC⟩)

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

/-! # Removing a diverging cutoff from a nonnegative weak L¹ sequence -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

private theorem indicator_test_integral {μ : Measure X} (s : Set X) (u : X → ℝ) :
    (∫ x, s.indicator (fun _ => (1 : ℝ)) x*u x ∂μ) = ∫ x, s.indicator u x ∂μ := by
  congr 1
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

theorem WeakL1Converges.moving_tail {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n x, 0 ≤ f n x) {r : X → ℝ} (hr : Measurable r)
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) :
    Tendsto (fun n => ∫ x, {x | b n ≤ r x}.indicator (f n) x ∂μ) atTop (𝓝 0) := by
  let s : ℕ → Set X := fun m => {x | (m : ℝ) ≤ r x}
  have hs m : MeasurableSet (s m) := measurableSet_le measurable_const hr
  have hgTail : Tendsto (fun m => ∫ x, (s m).indicator g x ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (f := fun _ : X => (0 : ℝ)) (fun x => ‖g x‖)
      (fun m => (h.2.1.aestronglyMeasurable.indicator (hs m))) h.2.1.norm
      (fun m => ae_of_all _ (fun x => by
        by_cases hx : x ∈ s m <;> simp [hx]))
      (ae_of_all _ (fun x => by
        obtain ⟨N,hN⟩ := exists_nat_gt (r x)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with m hm
        have hx : x ∉ s m := not_le.mpr (hN.trans_le (by exact_mod_cast hm))
        simp [hx]))
    simpa using ht
  have hfixed (m : ℕ) : Tendsto (fun n => ∫ x, (s m).indicator (f n) x ∂μ)
      atTop (𝓝 (∫ x, (s m).indicator g x ∂μ)) := by
    have ht := h.2.2 ((s m).indicator (fun _ => 1)) (measurable_const.indicator (hs m))
      ⟨1,fun x => by by_cases hx : x ∈ s m <;> simp [hx]⟩
    simpa only [indicator_test_integral] using ht
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (integral_nonneg
      (fun x => indicator_nonneg (fun x _ => hfn n x) x)))
  · intro ε hε
    obtain ⟨m,hm⟩ := (hgTail.eventually (gt_mem_nhds hε)).exists
    have hsmall := (hfixed m).eventually (gt_mem_nhds hm)
    filter_upwards [hsmall, hb.eventually (eventually_ge_atTop (m : ℝ))] with n hn hbn
    refine lt_of_le_of_lt ?_ hn
    apply integral_mono ((hf n).indicator (measurableSet_le measurable_const hr))
      ((hf n).indicator (hs m))
    intro x
    by_cases hx : b n ≤ r x
    · have hy : x ∈ s m := hbn.trans hx
      simp [hx,hy]
    · rw [indicator_of_notMem (show x ∉ {x | b n ≤ r x} from hx)]
      exact indicator_nonneg (fun x _ => hfn n x) x

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

theorem WeakL1Converges.timePrimitive {μ : Measure ℝ} {ν : Measure P}
    [IsFiniteMeasure μ] [SFinite ν] {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    (h : WeakL1Converges (μ.prod ν) f g) (hfm : ∀ n, Measurable (f n))
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) :
    WeakL1Converges (μ.prod ν) (fun n => timePrimitive μ (f n)) (timePrimitive μ g) := by
  have hex := h.prod_constant (ν := μ) hfi
  have htrans : WeakL1Converges ((μ.prod ν).prod μ)
      (fun n z => f n (z.2,z.1.2)) (fun z => g (z.2,z.1.2)) := by
    apply WeakL1Converges.of_comp_measurePreserving (timeExchange_measurePreserving μ ν)
      (fun n => (hfm n).comp (measurable_snd.prodMk measurable_fst.snd))
      (h.1.comp (measurable_snd.prodMk measurable_fst.snd))
    exact hex
  have hint n : Integrable (fun z : (ℝ × P) × ℝ => f n (z.2,z.1.2)) ((μ.prod ν).prod μ) :=
    (timeExchange_measurePreserving μ ν).integrable_comp_of_integrable ((hfi n).comp_fst μ)
  let k : (ℝ × P) × ℝ → ℝ := fun z => if z.2 ≤ z.1.1 then 1 else 0
  have hkm : Measurable k := measurable_const.ite
    (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  have hkb : ∀ z, |k z| ≤ 1 := by intro z; dsimp [k]; split <;> norm_num
  have ht := htrans.marginal hint hkm 1 hkb
  have he (u : ℝ × P → ℝ) :
      (fun z : ℝ × P => ∫ s, k (z,s)*u (s,z.2) ∂μ) = Published.timePrimitive μ u := by
    funext z
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp [k,Published.timePrimitive]
    split <;> simp
  have hseq : (fun n z => ∫ s, k (z,s)*f n (s,z.2) ∂μ) =
      (fun n => Published.timePrimitive μ (f n)) := funext (fun n => he (f n))
  rw [hseq,he g] at ht
  exact ht

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AverageMajorant
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
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

theorem tendsto_L1_product {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f g : ℕ → X → ℝ} {a b : X → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hgm : ∀ n, AEStronglyMeasurable (g n) μ)
    (ham : AEStronglyMeasurable a μ) (hbm : AEStronglyMeasurable b μ)
    (hf : Tendsto (fun n => eLpNorm (fun x => f n x-a x) 1 μ) atTop (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm (fun x => g n x-b x) 1 μ) atTop (𝓝 0))
    (hui : UniformIntegrable (fun n x => f n x*g n x) 1 μ) :
    Tendsto (fun n => eLpNorm (fun x => f n x*g n x-a x*b x) 1 μ) atTop (𝓝 0) := by
  have hfa : TendstoInMeasure μ f atTop a :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) hfm ham hf
  have hgb : TendstoInMeasure μ g atTop b :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) hgm hbm hg
  have hm := tendstoInMeasure_mul hfm hgm hfa hgb
  exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num)
    (fun n => (hfm n).mul (hgm n)) (hui.memLp_of_tendstoInMeasure hm) hui.unifIntegrable hm

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

/-! # Integrable velocity majorants for hard-sphere pair densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem pairDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (pairDensity f) := by unfold pairDensity; fun_prop

omit [MeasurableSpace X] in
theorem pairDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : X × (Velocity × Velocity)) : 0 ≤ pairDensity f z :=
  mul_nonneg (mul_nonneg (by positivity) (hf _)) (hf _)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

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

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r650ac2_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
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

/-! # Uniform integrability of both physical collision terms -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.Compactness

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem uniformIntegrable_mono_nonneg {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {f g : ℕ → Y → ℝ} (hgm : UniformIntegrable g 1 ν)
    (hfm : ∀ n, AEStronglyMeasurable (f n) ν)
    (hf : ∀ n, ∀ᵐ y ∂ν, 0 ≤ f n y)
    (hle : ∀ n, ∀ᵐ y ∂ν, f n y ≤ g n y) : UniformIntegrable f 1 ν := by
  have hb (n) : ∀ᵐ y ∂ν, ‖f n y‖ₑ ≤ ‖g n y‖ₑ := by
    filter_upwards [hf n,hle n] with y hy hly
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_of_nonneg hy,Real.norm_of_nonneg (hy.trans hly)]
    exact hly
  obtain ⟨hu,C,hC⟩ := hgm
  exact ⟨hu.ae_mono hfm hb,C,fun n =>
    (eLpNorm_mono_enorm_ae (hb n)).trans (hC n)⟩

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

theorem weak_preRate {μ : Measure X} [SFinite μ] {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hf : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => preRate (f n)) (preRate g) := by
  have hh := (h.prod_constant (ν := sphereArea) hf).bounded_mul normalizedKernel_measurable
    1 normalizedKernel_bound
  simpa only [← preRate_eq_normalized] using hh

theorem weak_postRate {μ : Measure X} [SFinite μ] {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hf : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => postRate (f n)) (postRate g) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (scatterTriple_measurePreserving μ)
    (fun n => (preRate_measurable (hfm n)).comp scatterTriple_measurable)
    ((preRate_measurable hgm).comp scatterTriple_measurable)
  have hs (z : (X × (Velocity × Velocity)) × Sphere) :
      scatterTriple (scatterTriple z) = z := scatterTriple_involutive z
  simpa only [postRate, Function.comp_def, hs] using weak_preRate h hf

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Weak convergence of the physical gain and loss marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_3_r650ac2_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TightApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform L¹ approximation preserves tightness on infinite measure spaces -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem unifTight_mono {f g : ℕ → X → ℝ}
    (hg : UnifTight g 1 μ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ₑ ≤ ‖g n x‖ₑ) : UnifTight f 1 μ := by
  intro ε hε
  obtain ⟨s,hs,hμs,hgs⟩ := hg.exists_measurableSet_indicator hε.ne'
  refine ⟨s,hμs.ne,fun n => ?_⟩
  apply le_trans (eLpNorm_mono_enorm_ae ?_) (hgs n)
  filter_upwards [hle n] with x hx
  by_cases hxs : x ∈ s
  · simp only [indicator_of_notMem (show x ∉ sᶜ from fun h => h hxs)]
    exact le_rfl
  · simpa only [indicator_of_mem (show x ∈ sᶜ from hxs)] using hx

end BoltzmannNonuniqueness.Compactness

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

omit [MeasurableSpace X] in
theorem pairProduct_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : X × (Velocity × Velocity)) : 0 ≤ pairProduct f z := mul_nonneg (hf _) (hf _)

omit [MeasurableSpace X] in
theorem pairProduct_le_pairDensity {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : X × (Velocity × Velocity)) : pairProduct f z ≤ pairDensity f z := by
  have h := mul_le_mul_of_nonneg_right
    (show (1:ℝ) ≤ 1+‖z.2.1‖+‖z.2.2‖ by linarith [norm_nonneg z.2.1,norm_nonneg z.2.2])
    (pairProduct_nonneg hf z)
  unfold pairProduct pairDensity at *
  nlinarith [h]

theorem pairProduct_uniformIntegrable {μ : Measure X} {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hpair : UniformIntegrable (fun n => pairDensity (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity)))) :
    UniformIntegrable (fun n => pairProduct (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) :=
  uniformIntegrable_mono_nonneg hpair
    (fun n => (pairProduct_measurable (hfm n)).aestronglyMeasurable)
    (fun n => ae_of_all _ (pairProduct_nonneg (hf n)))
    (fun n => ae_of_all _ (pairProduct_le_pairDensity (hf n)))

theorem pairProduct_unifTight {μ : Measure X} {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hpair : UnifTight (fun n => pairDensity (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity)))) :
    UnifTight (fun n => pairProduct (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
  apply Compactness.unifTight_mono hpair
    (fun n => (pairProduct_measurable (hfm n)).aestronglyMeasurable)
  intro n
  filter_upwards [] with z
  rw [Real.enorm_eq_ofReal (pairProduct_nonneg (hf n) z),
    Real.enorm_eq_ofReal (pairDensity_nonneg (hf n) z)]
  exact ENNReal.ofReal_le_ofReal (pairProduct_le_pairDensity (hf n) z)

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CutoffLossFrequency
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Identification of the cutoff loss marginal with collision frequency -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_5 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem integral_cutoffKernel (b : ℝ) (v w : Velocity) :
    (∫ ω : Sphere, CollisionCutoff.kernel b v w ω ∂sphereArea) =
      2*Real.pi*CollisionCutoff.rate b v w := by
  unfold CollisionCutoff.kernel CollisionCutoff.rate
  by_cases h : ‖v-w‖ < b
  · simp only [ite_eq_left h,integral_collisionKernel_sphereArea]
  · simp only [ite_eq_right h,integral_zero,mul_zero]

omit [MeasurableSpace X] in
theorem cutoffLossDensity_eq_frequency (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity)
    (hi : Integrable (fun q : Velocity × Sphere =>
      CollisionCutoff.kernel b p.2 q.1 q.2*f p*f (p.1,q.1))
      ((volume : Measure Velocity).prod sphereArea)) :
    cutoffLossDensity b f p = f p*KineticCollisionNullSets.frequency b f p := by
  unfold cutoffLossDensity
  rw [integral_prod _ hi]
  simp_rw [integral_mul_const,integral_cutoffKernel]
  calc
    _ = ∫ w : Velocity, (f p*(2*Real.pi))*(CollisionCutoff.rate b p.2 w*f (p.1,w)) := by
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    _ = _ := by
      rw [integral_const_mul]
      unfold KineticCollisionNullSets.frequency CollisionCutoff.frequency
      ring

theorem cutoff_loss_ae_eq_frequency {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) (b : ℝ) :
    cutoffLossDensity b f =ᵐ[μ.prod (volume : Measure Velocity)]
      fun p => f p*KineticCollisionNullSets.frequency b f p := by
  have hl : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => preRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (preRate_integrable hfm hf hpair)
  filter_upwards [hl.prod_right_ae] with p hp
  apply cutoffLossDensity_eq_frequency
  have hS : MeasurableSet {q : Velocity × Sphere | ‖p.2-q.1‖ < b} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hi := hp.indicator hS
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  by_cases h : ‖p.2-q.1‖ < b
  · rw [Set.indicator_of_mem (show q ∈ {q : Velocity × Sphere | ‖p.2-q.1‖ < b} from h)]
    simp only [CollisionCutoff.kernel,ite_eq_left h]
    rfl
  · rw [Set.indicator_of_notMem (show q ∉ {q : Velocity × Sphere | ‖p.2-q.1‖ < b} from h)]
    simp only [CollisionCutoff.kernel,ite_eq_right h,zero_mul]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MovingCutoffWeakLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak convergence survives the diverging physical cutoff -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.moving_cutoff {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n x, 0 ≤ f n x) {r : X → ℝ} (hr : Measurable r)
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) :
    WeakL1Converges μ (fun n => {x | r x < b n}.indicator (f n)) g := by
  refine ⟨h.1,h.2.1,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  let s : ℕ → Set X := fun n => {x | b n ≤ r x}
  have hs n : MeasurableSet (s n) := measurableSet_le measurable_const hr
  have ht := h.moving_tail hf hfn hr hb
  have herror : Tendsto (fun n => ∫ x, ψ x*(s n).indicator (f n) x ∂μ) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
    · intro n
      calc
        _ ≤ ∫ x, |C| *(s n).indicator (f n) x ∂μ := by
          apply norm_integral_le_of_norm_le ((hf n).indicator (hs n) |>.const_mul |C|)
          filter_upwards [] with x
          rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
          rw [abs_of_nonneg (indicator_nonneg (fun x _ => hfn n x) x)]
          exact mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C))
            (indicator_nonneg (fun x _ => hfn n x) x)
        _ = |C| *(∫ x, (s n).indicator (f n) x ∂μ) := integral_const_mul _ _
    · simpa using ht.const_mul |C|
  have hfull := h.2.2 ψ hψ ⟨C,hC⟩
  have he n : (∫ x, ψ x*{x | r x < b n}.indicator (f n) x ∂μ) =
      (∫ x, ψ x*f n x ∂μ)-(∫ x, ψ x*(s n).indicator (f n) x ∂μ) := by
    rw [← integral_sub ((hf n).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))
      (((hf n).indicator (hs n)).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))]
    congr 1
    ext x
    by_cases hx : r x < b n
    · have hy : x ∉ s n := not_le.mpr hx
      simp [hx,hy]
    · have hy : x ∈ s n := le_of_not_gt hx
      simp [hx,hy]
  simp_rw [he]
  simpa using hfull.sub herror

end BoltzmannNonuniqueness.Published

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

/-! # The moving relative-speed cutoff has the full collision limit -/

noncomputable section

open MeasureTheory Filter Set

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_6 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem truncatedPreRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) (b : ℝ) :
    Measurable (truncatedPreRate b f) :=
  (preRate_measurable hfm).indicator (measurableSet_lt (by fun_prop) measurable_const)

theorem truncatedPostRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) (b : ℝ) :
    Measurable (truncatedPostRate b f) :=
  ((preRate_measurable hfm).comp scatterTriple_measurable).indicator
    (measurableSet_lt (by fun_prop) measurable_const)

theorem cutoffGain_eq_marginal (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    KineticCollisionNullSets.gain b f p = ∫ q : Velocity × Sphere,
      truncatedPostRate b f (collisionGrouping.symm (p,q)) ∂volume.prod sphereArea := by
  apply integral_congr_ae
  filter_upwards [] with q
  change CollisionCutoff.kernel b p.2 q.1 q.2 * f (p.1,scatterLeft p.2 q.1 q.2) *
    f (p.1,scatterRight p.2 q.1 q.2) =
    if ‖p.2-q.1‖ < b then postRate f ((p.1,(p.2,q.1)),q.2) else 0
  rw [postRate_formula]
  by_cases hq : ‖p.2-q.1‖ < b <;> simp [CollisionCutoff.kernel,hq]

theorem cutoffLoss_eq_marginal (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    cutoffLossDensity b f p = ∫ q : Velocity × Sphere,
      truncatedPreRate b f (collisionGrouping.symm (p,q)) ∂volume.prod sphereArea := by
  apply integral_congr_ae
  filter_upwards [] with q
  change CollisionCutoff.kernel b p.2 q.1 q.2*f p*f (p.1,q.1) =
    if ‖p.2-q.1‖ < b then preRate f ((p.1,(p.2,q.1)),q.2) else 0
  by_cases hq : ‖p.2-q.1‖ < b <;> simp [CollisionCutoff.kernel,preRate,hq]

theorem weak_cutoff_gainLoss {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfn : ∀ n z, 0 ≤ f n z) (hgm : Measurable g)
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hf : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity))))
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) :
    Published.WeakL1Converges (μ.prod volume)
      (fun n => KineticCollisionNullSets.gain (b n) (f n)) (gainDensity g) ∧
      Published.WeakL1Converges (μ.prod volume)
      (fun n => cutoffLossDensity (b n) (f n)) (lossDensity g) := by
  have hr : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => ‖z.1.2.1-z.1.2.2‖) := by
    fun_prop
  have hpre := (weak_preRate h hf).moving_cutoff
    (fun n => preRate_integrable (hfm n) (hfn n) (hf n))
    (fun n z => preRate_nonneg (hfn n) z) hr hb
  have hpost := (weak_postRate hfm hgm h hf).moving_cutoff
    (fun n => postRate_integrable (hfm n) (hfn n) (hf n))
    (fun n z => preRate_nonneg (hfn n) (scatterTriple z)) hr hb
  have hpre' := weak_grouped_rate (fun n => truncatedPreRate_measurable (hfm n) (b n))
    (preRate_measurable hgm) hpre
  have hpost' := weak_grouped_rate (fun n => truncatedPostRate_measurable (hfm n) (b n))
    ((preRate_measurable hgm).comp scatterTriple_measurable) hpost
  have hs n : MeasurableSet {z : (X × (Velocity × Velocity)) × Sphere |
      ‖z.1.2.1-z.1.2.2‖ < b n} := measurableSet_lt hr measurable_const
  have hpInt n := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    ((postRate_integrable (hfm n) (hfn n) (hf n)).indicator (hs n))
  have hlInt n := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    ((preRate_integrable (hfm n) (hfn n) (hf n)).indicator (hs n))
  have hp := hpost'.marginal hpInt (k := fun _ => 1) measurable_const 1 (fun _ => by norm_num)
  have hl := hpre'.marginal hlInt (k := fun _ => 1) measurable_const 1 (fun _ => by norm_num)
  simp only [one_mul,← cutoffGain_eq_marginal,← cutoffLoss_eq_marginal] at hp hl
  exact ⟨hp,hl⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SmoothTestFamily
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.sphereArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countably many compact smooth cutoffs covering an open spacetime region -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Compactness

theorem exists_spacetime_cutoff_cover {U : Set Published.SpaceTime}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ χ : ℕ → Published.SpaceTime → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n, tsupport (χ n) ⊆ U) ∧ (∀ x ∈ U, ∃ n, χ n x ≠ 0) := by
  let ι := {f : Published.SpaceTime → ℝ // tsupport f ⊆ U ∧ HasCompactSupport f ∧
    ContDiff ℝ (⊤ : ℕ∞) f}
  have hcover : (⋃ f : ι, Function.support (f : Published.SpaceTime → ℝ)) = U := by
    apply Subset.antisymm
    · exact iUnion_subset (fun f => (subset_tsupport f.1).trans f.2.1)
    · intro x hx
      obtain ⟨f,hfs,hfc,hfd,_hfR,hfx⟩ :=
        exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds hx)
      let b : ι := ⟨f,hfs,hfc,hfd⟩
      exact mem_iUnion_of_mem b (by simp only [b,Function.mem_support,hfx,ne_eq,one_ne_zero,not_false_eq_true])
  obtain ⟨S,hSc,hS⟩ : ∃ S : Set ι, S.Countable ∧
      (⋃ f ∈ S, Function.support (f : Published.SpaceTime → ℝ)) = U := by
    obtain ⟨S,hSc,hS⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun f : ι => Function.support f.1)
      (fun f : ι => f.2.2.2.continuous.isOpen_support)
    exact ⟨S,hSc,hS.trans hcover⟩
  have hSne : S.Nonempty := by
    by_contra he
    have hse : S = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    simp only [hse,mem_empty_iff_false,iUnion_of_empty,iUnion_empty] at hS
    exact hne.ne_empty hS.symm
  obtain ⟨a,ha⟩ := Set.Countable.exists_eq_range hSc hSne
  refine ⟨fun n => (a n).1,fun n => (a n).2.2.2,fun n => (a n).2.2.1,
    fun n => (a n).2.1,?_⟩
  intro x hx
  rw [← hS,ha] at hx
  obtain ⟨f,hf,hfx⟩ := mem_iUnion₂.mp hx
  obtain ⟨n,rfl⟩ := hf
  exact ⟨n,hfx⟩

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # A countable smooth compact family determining integrable velocity densities -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

private theorem smoothTest_smooth (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smoothTest j) :=
  (supportedSeq (Nat.unpair j).1 (Nat.unpair j).2).2.1

private theorem smoothTest_compact (j : ℕ) : HasCompactSupport (smoothTest j) :=
  (isCompact_closedBall (0 : Velocity) ((Nat.unpair j).1+1 : ℝ)).of_isClosed_subset
    (isClosed_tsupport _) (supportedSeq (Nat.unpair j).1 (Nat.unpair j).2).2.2

theorem exists_countable_smooth_determining_tests :
    ∃ ψ : ℕ → Velocity → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) ∧
      (∀ j, HasCompactSupport (ψ j)) ∧
      ∀ u : Velocity → ℝ, Integrable u →
        (∀ j, ∫ v, ψ j v*u v = 0) → u =ᵐ[volume] 0 := by
  refine ⟨smoothTest,smoothTest_smooth,smoothTest_compact,?_⟩
  intro u hu hzero
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable
  intro ψ hψ hψc
  obtain ⟨R,_hR,hball⟩ := hψc.isBounded.subset_ball_lt 0 (0 : Velocity)
  obtain ⟨n,hn⟩ := exists_nat_gt R
  have hsupp : tsupport ψ ⊆ Metric.closedBall (0 : Velocity) (n+1 : ℝ) := by
    intro v hv
    have hvr : ‖v‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hball hv
    rw [Metric.mem_closedBall,dist_zero_right]
    linarith
  let t : SupportedTest n := ⟨⟨ψ,hψ.continuous⟩,hψ,hsupp⟩
  have hd : DenseRange (supportedSeq n) := TopologicalSpace.denseRange_denseSeq (SupportedTest n)
  obtain ⟨a,ha,hat⟩ := mem_closure_iff_seq_limit.mp (hd t)
  choose b hb using ha
  have hat' : Tendsto (fun m => (supportedSeq n (b m)).1) atTop (𝓝 t.1) := by
    have he : (fun m => supportedSeq n (b m)) = a := funext hb
    have hat0 : Tendsto (fun m => supportedSeq n (b m)) atTop (𝓝 t) := by
      rw [he]
      exact hat
    exact continuous_subtype_val.continuousAt.tendsto.comp hat0
  have ht := tendsto_integral_mul_common_support hu
    (isCompact_closedBall (0 : Velocity) (n+1 : ℝ))
    (fun m => (supportedSeq n (b m)).2.2) hsupp hat'
  have hz (m) : (∫ v, (supportedSeq n (b m)).1 v*u v) = 0 := by
    have hz := hzero (Nat.pair n (b m))
    unfold smoothTest at hz
    rw [Nat.unpair_pair] at hz
    exact hz
  simp_rw [hz] at ht
  have hlim : (0 : ℝ) = ∫ v, ψ v*u v := tendsto_nhds_unique tendsto_const_nhds ht
  simpa only [smul_eq_mul] using hlim.symm

end BoltzmannNonuniqueness.Compactness

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

theorem weak_along {μ : Measure ℝ} [SFinite μ] {F : ℕ → ℝ × Phase → ℝ} {g : ℝ × Phase → ℝ}
    (hF : ∀ n, Measurable (F n)) (h : Published.WeakL1Converges (μ.prod volume) F g) :
    Published.WeakL1Converges (μ.prod volume) (fun n => along (F n)) (along g) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (back_measurePreserving μ)
    (fun n => (hF n).comp (along_measurePreserving μ).measurable)
    (h.1.comp (along_measurePreserving μ).measurable)
  simpa only [along,Function.comp_def,neg_flight] using h

end BoltzmannNonuniqueness.TorusFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalMomentIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Passing from all compact restrictions to an almost-everywhere assertion -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Compactness

theorem ae_of_all_compact_restrict {μ : Measure Published.SpaceTime} {p : Published.SpaceTime → Prop}
    (h : ∀ K : Set Published.SpaceTime, IsCompact K → ∀ᵐ x ∂μ.restrict K, p x) :
    ∀ᵐ x ∂μ, p x := by
  have he : (⋃ n : ℕ, Metric.closedBall (0 : Published.SpaceTime) n) = univ :=
    Metric.iUnion_closedBall_nat 0
  have ht := (ae_restrict_iUnion_iff (fun n : ℕ => Metric.closedBall (0 : Published.SpaceTime) n) p).mpr
    (fun n => h _ (isCompact_closedBall _ _))
  simpa only [he,Measure.restrict_univ] using ht

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairPatchIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countable tensor tests determine an integrable velocity-pair density -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Compactness

theorem pair_tests_determine {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    {F : Velocity × Velocity → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    (hz : ∀ i j, ∫ z, (ψ i z.1*ψ j z.2)*F z = 0) : F =ᵐ[volume] 0 := by
  have hF : Integrable F ((volume : Measure Velocity).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hFi
  have hbound (i) : ∃ C : ℝ, ∀ v, |ψ i v| ≤ C :=
    (hψ i).continuous.bounded_above_of_compact_support (hc i)
  have hm (i) : Integrable (fun z : Velocity × Velocity => ψ i z.1*F z)
      ((volume : Measure Velocity).prod volume) := by
    obtain ⟨C,hC⟩ := hbound i
    exact hF.bdd_mul ((hψ i).continuous.measurable.comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ (fun z => hC z.1))
  have hzero (i) : (fun w => ∫ v, ψ i v*F (v,w)) =ᵐ[volume] 0 := by
    apply hdet _ (hm i).integral_prod_right
    intro j
    obtain ⟨D,hD⟩ := hbound j
    have hmul := (hm i).bdd_mul
      ((hψ j).continuous.measurable.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ (fun z => hD z.2))
    change Integrable (fun z : Velocity × Velocity => ψ j z.2*(ψ i z.1*F z))
      ((volume : Measure Velocity).prod volume) at hmul
    calc
      _ = ∫ z : Velocity × Velocity, ψ j z.2*(ψ i z.1*F z)
          ∂((volume : Measure Velocity).prod volume) := by
        rw [integral_prod_symm _ hmul]
        simp_rw [integral_const_mul]
      _ = ∫ z : Velocity × Velocity, (ψ i z.1*ψ j z.2)*F z := by
        rw [Measure.volume_eq_prod]
        congr 1
        ext z
        ring
      _ = 0 := hz i j
  have hs : MeasurableSet {z : Velocity × Velocity | F z = 0} := hFm (isClosed_singleton.measurableSet)
  have hfib : ∀ᵐ w ∂(volume : Measure Velocity), ∀ᵐ v ∂(volume : Measure Velocity), F (v,w) = 0 := by
    filter_upwards [ae_all_iff.mpr hzero,hF.prod_left_ae] with w hw hfw
    exact hdet (fun v => F (v,w)) hfw hw
  have hall : ∀ᵐ z ∂((volume : Measure Velocity).prod volume), F z = 0 :=
    (Measure.ae_prod_iff_ae_ae hs).mpr ((Measure.ae_ae_comm hs).mpr hfib)
  rw [Measure.volume_eq_prod]
  exact hall

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Tensor moments identify the full velocity-pair product -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Compactness

theorem pair_eq_product_of_moments {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    {W : Velocity × Velocity → ℝ} {g : Velocity → ℝ}
    (hWm : Measurable W) (hgm : Measurable g) (hWi : Integrable W) (hgi : Integrable g)
    (hmom : ∀ i j, (∫ z, (ψ i z.1*ψ j z.2)*W z) =
      (∫ v, ψ i v*g v)*(∫ w, ψ j w*g w)) :
    W =ᵐ[volume] (fun z => g z.1*g z.2) := by
  have hgmul : Integrable (fun z : Velocity × Velocity => g z.1*g z.2) := by
    rw [Measure.volume_eq_prod]
    exact hgi.mul_prod hgi
  have hprodMeas : Measurable (fun z : Velocity × Velocity => g z.1*g z.2) := by fun_prop
  have hd := hWi.sub hgmul
  have hdm := hWm.sub hprodMeas
  have htest (i j) {u : Velocity × Velocity → ℝ} (hi : Integrable u) :
      Integrable (fun z : Velocity × Velocity => (ψ i z.1*ψ j z.2)*u z) := by
    obtain ⟨C,hC⟩ := (hψ i).continuous.bounded_above_of_compact_support (hc i)
    obtain ⟨D,hD⟩ := (hψ j).continuous.bounded_above_of_compact_support (hc j)
    apply hi.bdd_mul (by fun_prop)
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul ((hC z.1).trans (le_abs_self C)) ((hD z.2).trans (le_abs_self D))
        (abs_nonneg _) (abs_nonneg _))
  have hz (i j) : (∫ z : Velocity × Velocity,
      (ψ i z.1*ψ j z.2)*(W z-g z.1*g z.2)) = 0 := by
    have hsplit : (fun z : Velocity × Velocity => (ψ i z.1*ψ j z.2)*(W z-g z.1*g z.2)) =
        fun z => (ψ i z.1*ψ j z.2)*W z-(ψ i z.1*ψ j z.2)*(g z.1*g z.2) := by
      funext z
      ring
    rw [hsplit,integral_sub (htest i j hWi) (htest i j hgmul),hmom i j]
    have he : (∫ z : Velocity × Velocity, (ψ i z.1*ψ j z.2)*(g z.1*g z.2)) =
        (∫ v, ψ i v*g v)*(∫ w, ψ j w*g w) := by
      calc
        _ = ∫ z : Velocity × Velocity, (ψ i z.1*g z.1)*(ψ j z.2*g z.2) := by
          congr 1
          ext z
          ring
        _ = _ := by
          rw [Measure.volume_eq_prod]
          exact integral_prod_mul (fun v => ψ i v*g v) (fun w => ψ j w*g w)
    rw [he,sub_self]
  have he := pair_tests_determine hψ hc hdet hdm hd hz
  filter_upwards [he] with z hz
  exact sub_eq_zero.mp hz

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Removing a nonzero spacetime cutoff from tensor moments -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Compactness

theorem unscale_pair_moment {W : Velocity × Velocity → ℝ} {g p q : Velocity → ℝ}
    {c : ℝ} (hc : c ≠ 0)
    (h : (∫ y : Velocity × Velocity, ((c*p y.1)*(c*q y.2))*W y) =
      (∫ v, (c*p v)*g v)*(∫ w, (c*q w)*g w)) :
    (∫ y : Velocity × Velocity, (p y.1*q y.2)*W y) =
      (∫ v, p v*g v)*(∫ w, q w*g w) := by
  have hleft : (fun y : Velocity × Velocity => ((c*p y.1)*(c*q y.2))*W y) =
      fun y => (c*c)*((p y.1*q y.2)*W y) := by funext y; ring
  have hp : (∫ v, (c*p v)*g v) = c*(∫ v, p v*g v) := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  have hq : (∫ v, (c*q v)*g v) = c*(∫ v, q v*g v) := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  rw [hleft,integral_const_mul,hp,hq] at h
  apply mul_left_cancel₀ (mul_ne_zero hc hc)
  calc
    _ = (c*(∫ v, p v*g v))*(c*(∫ w, q w*g w)) := h
    _ = _ := by ring

theorem pair_identity_on_patch {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    {W : X × (Velocity × Velocity) → ℝ} {g : X × Velocity → ℝ}
    (hWm : Measurable W) (hgm : Measurable g)
    (hWi : Integrable W (μ.prod volume)) (hgi : Integrable g (μ.prod volume))
    (χ : X → ℝ)
    (hmom : ∀ i j, ∀ᵐ x ∂μ, χ x ≠ 0 →
      (∫ y : Velocity × Velocity, ((χ x*ψ i y.1)*(χ x*ψ j y.2))*W (x,y)) =
        (∫ v, (χ x*ψ i v)*g (x,v))*(∫ w, (χ x*ψ j w)*g (x,w))) :
    ∀ᵐ x ∂μ, χ x ≠ 0 → (fun y => W (x,y)) =ᵐ[volume]
      (fun y : Velocity × Velocity => g (x,y.1)*g (x,y.2)) := by
  have hm : ∀ᵐ x ∂μ, ∀ i j, χ x ≠ 0 →
      (∫ y : Velocity × Velocity, ((χ x*ψ i y.1)*(χ x*ψ j y.2))*W (x,y)) =
        (∫ v, (χ x*ψ i v)*g (x,v))*(∫ w, (χ x*ψ j w)*g (x,w)) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hmom i))
  filter_upwards [hm,hWi.prod_right_ae,hgi.prod_right_ae] with x hx hWx hgx hχ
  apply pair_eq_product_of_moments hψ hc hdet
    (hWm.comp measurable_prodMk_left) (hgm.comp measurable_prodMk_left) hWx hgx
  intro i j
  exact unscale_pair_moment hχ (hx i j hχ)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocitySmoothingError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Smooth compact velocity cutoffs preserving a prescribed test -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Compactness

theorem exists_velocity_cutoff {ψ : Velocity → ℝ} (hc : HasCompactSupport ψ) :
    ∃ β : Velocity → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
      (∀ v, 0 ≤ β v) ∧ (∀ v, ψ v*β v = ψ v) := by
  obtain ⟨R,hR,hball⟩ := hc.isBounded.subset_ball_lt 0 (0 : Velocity)
  let b : ContDiffBump (0 : Velocity) := ⟨R,R+1,hR,by linarith⟩
  refine ⟨b,b.contDiff,b.hasCompactSupport,fun v => b.nonneg,fun v => ?_⟩
  by_cases hv : v ∈ tsupport ψ
  · have hb : v ∈ Metric.closedBall (0 : Velocity) b.rIn :=
      Metric.ball_subset_closedBall (hball hv)
    rw [b.one_of_mem_closedBall hb,mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hv,zero_mul]

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TransportCutoff
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of smooth kinetic cutoffs along free characteristics -/

noncomputable section

open Set
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

theorem characteristic_hasDerivAt (p : _root_.OAI.BoltzmannNonuniqueness.Published.Velocity × _root_.OAI.BoltzmannNonuniqueness.Published.Velocity) (t : ℝ) :
    HasDerivAt (characteristic p) ((1,p.2),0) t := by
  have hx : HasDerivAt (fun s : ℝ => p.1+s • p.2) p.2 t := by
    simpa using ((hasDerivAt_id t).smul_const p.2).const_add p.1
  exact ((hasDerivAt_id t).prodMk hx).prodMk (hasDerivAt_const t p.2)

theorem hasDerivAt_along {χ : KineticPhase → ℝ} (hχ : Differentiable ℝ χ)
    (p : _root_.OAI.BoltzmannNonuniqueness.Published.Velocity × _root_.OAI.BoltzmannNonuniqueness.Published.Velocity) (t : ℝ) :
    HasDerivAt (fun s => χ (characteristic p s))
      (transportDerivative χ (characteristic p t)) t :=
  (hχ (characteristic p t)).hasFDerivAt.comp_hasDerivAt t (characteristic_hasDerivAt p t)

theorem characteristic_continuous (p : _root_.OAI.BoltzmannNonuniqueness.Published.Velocity × _root_.OAI.BoltzmannNonuniqueness.Published.Velocity) : Continuous (characteristic p) :=
  continuous_iff_continuousAt.mpr (fun t => (characteristic_hasDerivAt p t).continuousAt)

theorem transportDerivative_eq_zero {χ : KineticPhase → ℝ} {z : KineticPhase}
    (hz : z ∉ tsupport χ) : transportDerivative χ z = 0 := by
  unfold transportDerivative
  rw [fderiv_of_notMem_tsupport ℝ hz]
  rfl

theorem transportDerivative_continuous {χ : KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) : Continuous (transportDerivative χ) := by
  have hd : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hd.clm_apply (by fun_prop)

theorem transportDerivative_hasCompactSupport {χ : KineticPhase → ℝ}
    (hχ : HasCompactSupport χ) : HasCompactSupport (transportDerivative χ) := by
  apply hχ.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_tsupport χ)
  intro z hz
  by_contra hn
  exact hz (transportDerivative_eq_zero hn)

end BoltzmannNonuniqueness.TransportCutoff

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedGainSmoothingAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Causal localized transport sources and their velocity support -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

theorem localizedSource_causal (U : ℝ) (χ f Q : KineticPhase → ℝ)
    (z : KineticPhase) (ht : z.1.1 < 0) : localizedSource U χ f Q z = 0 := by
  apply ite_eq_right
  exact fun h => not_le_of_gt ht h.1

theorem localizedSource_on {U : ℝ} (χ f Q : KineticPhase → ℝ)
    (z : KineticPhase) (ht : z.1.1 ∈ Icc 0 U) :
    localizedSource U χ f Q z = χ z*Q z+(transportDerivative χ z+χ z)*f z := ite_eq_left ht

theorem localizedSource_velocity_support {U R : ℝ} {χ : KineticPhase → ℝ}
    (hχ : tsupport χ ⊆ {z | ‖z.2‖ ≤ R}) (f Q : KineticPhase → ℝ)
    (z : KineticPhase) (hv : R < ‖z.2‖) : localizedSource U χ f Q z = 0 := by
  have hz : z ∉ tsupport χ := fun h => not_le_of_gt hv (hχ h)
  have hc : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
  have hd := transportDerivative_eq_zero hz
  unfold localizedSource
  split_ifs <;> simp only [hc,hd,zero_mul,add_zero]

theorem localizedSource_measurable {U : ℝ} {χ f Q : KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hf : Measurable f) (hQ : Measurable Q) :
    Measurable (localizedSource U χ f Q) := by
  apply Measurable.ite
  · exact measurableSet_Icc.preimage measurable_fst.fst
  · exact (hχ.continuous.measurable.mul hQ).add
      (((transportDerivative_continuous hχ).measurable.add hχ.continuous.measurable).mul hf)
  · exact measurable_const

end BoltzmannNonuniqueness.TransportCutoff

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CutoffLipschitz
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local weighted Lipschitz bounds for the finite-cutoff equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CutoffLipschitz

theorem frequencyConstant_nonneg {b : ℝ} (hb : 0 ≤ b) (q : ℝ) : 0 ≤ frequencyConstant q b := by
  unfold frequencyConstant
  have hi : 0 ≤ ∫ w, H q w := integral_nonneg (H_nonneg q)
  positivity

theorem integrable_dominated {q A : ℝ} (hq : q < 2) {f : Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w) (hfB : ∀ w, f w ≤ A * H q w) : Integrable f := by
  apply ((integrable_H hq).const_mul A).mono' hfm.aestronglyMeasurable
  filter_upwards [] with w
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf w)] using hfB w

theorem frequency_nonneg {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (b : ℝ) (v : Velocity) :
    0 ≤ CollisionCutoff.frequency b f v := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun w => mul_nonneg (CollisionCutoff.rate_nonneg b v w) (hf w))

theorem frequency_bound {q A b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (hfB : ∀ w, f w ≤ A * H q w) (v : Velocity) :
    CollisionCutoff.frequency b f v ≤ A * frequencyConstant q b := by
  have hi := integrable_dominated hq hfm hf hfB
  calc
    _ ≤ 2 * Real.pi * b * ∫ w, |f w| :=
      (le_abs_self _).trans (CollisionCutoff.abs_frequency_le hb hi v)
    _ ≤ 2 * Real.pi * b * ∫ w, A * H q w := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono hi.abs ((integrable_H hq).const_mul A)
        (fun w => by simpa only [abs_of_nonneg (hf w)] using hfB w)
    _ = _ := by rw [integral_const_mul]; unfold frequencyConstant; ring

end BoltzmannNonuniqueness.CutoffLipschitz

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

/-! # Uniform integrability of the actual cutoff equation's right-hand side -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem collisionSource_measurable {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (collisionSource b f) :=
  (KineticCollisionNullSets.measurable_gain hf b).sub
    (hf.mul (KineticCollisionNullSets.measurable_frequency hf b))

private theorem uniformIntegrable_sub {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {f g : ℕ → Y → ℝ} (hf : UniformIntegrable f 1 ν) (hg : UniformIntegrable g 1 ν) :
    UniformIntegrable (fun n y => f n y-g n y) 1 ν := by
  obtain ⟨hu,C,hC⟩ := hf
  obtain ⟨hv,D,hD⟩ := hg
  refine ⟨hu.sub hv (by norm_num),C+D,fun n => ?_⟩
  exact (eLpNorm_sub_le (hf := hu.aestronglyMeasurable n) (hg := hv.aestronglyMeasurable n) (by norm_num : (1 : ℝ≥0∞) ≤ 1)).trans
    (by simpa only [ENNReal.coe_add] using add_le_add (hC n) (hD n))

theorem collisionSource_uniformIntegrable [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hpair : UniformIntegrable (fun n => pairDensity (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity)))) (b : ℕ → ℝ)
    (hgain : UniformIntegrable (fun n => KineticCollisionNullSets.gain (b n) (f n)) 1
      (μ.prod (volume : Measure Velocity)))
    (hloss : UniformIntegrable (fun n => cutoffLossDensity (b n) (f n)) 1
      (μ.prod (volume : Measure Velocity))) :
    UniformIntegrable (fun n => collisionSource (b n) (f n)) 1
      (μ.prod (volume : Measure Velocity)) := by
  have he (n) := cutoff_loss_ae_eq_frequency (hfm n) (hf n)
    (memLp_one_iff_integrable.mp (hpair.memLp n)) (b n)
  exact uniformIntegrable_sub hgain (hloss.ae_eq he)

end BoltzmannNonuniqueness.CollisionCompactness

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

/-! # Factorization of weak pair moments from strong velocity averages -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem weak_pair_moment_factorization {μ : Measure X} {ν : Measure Y}
    [IsFiniteMeasure μ] [SFinite ν]
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ} {W : X × (Y × Y) → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hpi : ∀ n, Integrable (fun z : X × (Y × Y) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) (μ.prod (ν.prod ν)))
    (hg : WeakL1Converges (μ.prod ν) f g)
    (hW : WeakL1Converges (μ.prod (ν.prod ν))
      (fun n z => f n (z.1,z.2.1)*f n (z.1,z.2.2)) W)
    {k l : X × Y → ℝ} (hk : Measurable k) (hl : Measurable l)
    (C D : ℝ) (hC : ∀ z, |k z| ≤ C) (hD : ∀ z, |l z| ≤ D)
    {A B : X → ℝ} (hAi : Integrable A μ) (hBi : Integrable B μ)
    (hA : Tendsto (fun n => eLpNorm (fun x => (∫ v, k (x,v)*f n (x,v) ∂ν)-A x) 1 μ)
      atTop (𝓝 0))
    (hB : Tendsto (fun n => eLpNorm (fun x => (∫ v, l (x,v)*f n (x,v) ∂ν)-B x) 1 μ)
      atTop (𝓝 0))
    (hui : UniformIntegrable (fun n x => (∫ v, k (x,v)*f n (x,v) ∂ν)*
      (∫ w, l (x,w)*f n (x,w) ∂ν)) 1 μ) :
    (fun x => ∫ y : Y × Y, (k (x,y.1)*l (x,y.2))*W (x,y) ∂ν.prod ν) =ᵐ[μ]
      (fun x => (∫ v, k (x,v)*g (x,v) ∂ν)*(∫ w, l (x,w)*g (x,w) ∂ν)) := by
  have hki (n) := ((hfi n).bdd_mul hk.aestronglyMeasurable (ae_of_all _ hC)).integral_prod_left
  have hli (n) := ((hfi n).bdd_mul hl.aestronglyMeasurable (ae_of_all _ hD)).integral_prod_left
  have hkg := (hg.marginal hfi hk C hC).eq_of_strong hki hAi hA
  have hlg := (hg.marginal hfi hl D hD).eq_of_strong hli hBi hB
  let kl : X × (Y × Y) → ℝ := fun z => k (z.1,z.2.1)*l (z.1,z.2.2)
  have hkl : Measurable kl := by dsimp [kl]; fun_prop
  have hklB : ∀ z, |kl z| ≤ |C| * |D| := by
    intro z
    dsimp [kl]
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self C)) ((hD _).trans (le_abs_self D))
      (abs_nonneg _) (abs_nonneg _)
  have hwp := hW.marginal hpi hkl (|C| * |D|) hklB
  have he (n) (x) : (∫ y : Y × Y, kl (x,y)*(f n (x,y.1)*f n (x,y.2)) ∂ν.prod ν) =
      (∫ v, k (x,v)*f n (x,v) ∂ν)*(∫ w, l (x,w)*f n (x,w) ∂ν) := by
    rw [← integral_prod_mul]
    congr 1
    ext y
    dsimp [kl]
    ring
  simp_rw [he] at hwp
  have hkm (n) : AEStronglyMeasurable (fun x => ∫ v, k (x,v)*f n (x,v) ∂ν) μ :=
    ((hk.mul (hfm n)).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hlm (n) : AEStronglyMeasurable (fun x => ∫ v, l (x,v)*f n (x,v) ∂ν) μ :=
    ((hl.mul (hfm n)).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hp := Compactness.tendsto_L1_product hkm hlm hAi.1 hBi.1 hA hB hui
  have hmi := hui.integrable_of_tendstoInMeasure
    (tendstoInMeasure_of_tendsto_eLpNorm (hf := fun _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num : (1:ℝ≥0∞) ≠ 0) hp)
  have hpEq := hwp.eq_of_strong (fun n => memLp_one_iff_integrable.mp (hui.memLp n)) hmi hp
  filter_upwards [hpEq,hkg,hlg] with x hx hkx hlx
  exact hx.symm.trans (by rw [hkx,hlx])

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

section

/-! # Smooth localization changes damping to the unit transport resolvent -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

/-- A smooth cutoff of a measurable-forcing mild solution has an explicit
unit-damped formula. This is the scalar part of the GLPS localization. -/
theorem localized_damped {T L c : ℝ} (hT : 0 ≤ T) {g χ χ' : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T)
    (hχ : ContinuousOn χ (Icc 0 T)) (hχ' : ContinuousOn χ' (Icc 0 T))
    (hdχ : ∀ t ∈ Icc 0 T, HasDerivAt χ (χ' t) t) :
    χ T*damped L c g T = Real.exp (-T)*χ 0*c +
      ∫ t in 0..T, Real.exp (-(T-t)) *
        (χ t*g t + (χ' t+(1-L)*χ t)*damped L c g t) := by
  let ψ : ℝ → ℝ := fun t => Real.exp t*χ t
  let ψ' : ℝ → ℝ := fun t => Real.exp t*(χ' t+χ t)
  have hψ : ContinuousOn ψ (Icc 0 T) := (by fun_prop : Continuous (Real.exp)).continuousOn.mul hχ
  have hψ' : ContinuousOn ψ' (Icc 0 T) := (by fun_prop : Continuous (Real.exp)).continuousOn.mul (hχ'.add hχ)
  have hdψ : ∀ t ∈ Icc 0 T, HasDerivAt ψ (ψ' t) t := by
    intro t ht
    convert (Real.hasDerivAt_exp t).mul (hdχ t ht) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [ψ,ψ']
    ring
  have H := damped_integration_by_parts hT hg hψ hψ' hdψ (L := L) (c := c)
  have he : Real.exp (-T)*Real.exp T = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hcalc : Real.exp (-T)*(∫ t in 0..T,
      ψ' t*damped L c g t+ψ t*(g t-L*damped L c g t)) =
      ∫ t in 0..T, Real.exp (-(T-t)) *
        (χ t*g t+(χ' t+(1-L)*χ t)*damped L c g t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [ψ,ψ']
    have hexp : Real.exp (-(T-t)) = Real.exp (-T)*Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  rw [H] at hcalc
  dsimp [ψ] at hcalc
  rw [Real.exp_zero,one_mul] at hcalc
  have hmul : Real.exp (-T)*(Real.exp T*χ T*damped L c g T) = χ T*damped L c g T := by
    calc
      _ = (Real.exp (-T)*Real.exp T)*χ T*damped L c g T := by ring
      _ = _ := by rw [he,one_mul]
  rw [mul_sub,hmul] at hcalc
  linarith

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianLocalExistence
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive local cutoff iteration along the actual free transport -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.GaussianLocal

theorem measurable_state {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) :
    Measurable (state f) := hf.comp (by fun_prop)

theorem measurable_flight : Measurable (fun z : ℝ × JetPrototype.Phase => JetBarrier.flight z.1 z.2) := by
  unfold JetBarrier.flight VelocityWeight.transverse VelocityWeight.axial
  fun_prop

end BoltzmannNonuniqueness.GaussianLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PhaseDecompositionNorm
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded representatives that realize the essential upper bound -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem ae_abs_le_size {f : JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hf : ∀ p, |f p| ≤ R) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f p| ≤ size f := by
  have hm : MemLp f ∞ FlightMeasure.phaseVolume :=
    memLp_top_of_bound hfm.aestronglyMeasurable R (ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs] using hf p))
  simpa only [Real.norm_eq_abs,← toReal_eLpNorm hm.1,size] using ae_le_lpNorm_exponent_top hm

end BoltzmannNonuniqueness.PhaseEssSup

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotPhysicalSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A fixed negligible velocity set for the weighted local construction

The exceptional set depends only on H and its proved quadratic gain bound,
not on a solution or an iterate. Setting the gain to zero there preserves
its almost-everywhere collision meaning and gives pointwise bounded sources.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotRepresentative

theorem measurable_nonnegativeGain {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) : Measurable (nonnegativeGain f g) := by
  let : SFinite (gainPairMeasure) := Measure.prod.instSFinite
  have hl : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      scatterLeft p.1 p.2.1 p.2.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hr : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      scatterRight p.1 p.2.1 p.2.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      ENNReal.ofReal (collisionKernel p.1 p.2.1 p.2.2) / 2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hk.mul (((hf.comp hl).mul (hg.comp hr)).add
    ((hg.comp hl).mul (hf.comp hr)))).lintegral_prod_right'

theorem measurableSet_good (q : ℝ) : MeasurableSet (good q) :=
  measurableSet_le (measurable_nonnegativeGain (measurable_H q).ennreal_ofReal
    (measurable_H q).ennreal_ofReal)
    ((measurable_H q).const_mul (HotApplication.realBound q)).ennreal_ofReal

theorem integrable_H_gain {q : ℝ} {v : Velocity} (hv : v ∈ good q) :
    Integrable (GainOrder.integrand (H q) v) ((volume : Measure Velocity).prod sphereArea) :=
  GainNonnegative.integrable_of_bound (measurable_H q) (H_nonneg q) v hv

theorem H_gain_bound {q : ℝ} {v : Velocity} (hv : v ∈ good q) :
    BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v ≤ HotApplication.realBound q * H q v :=
  GainNonnegative.gain_le_of_bound (measurable_H q) (H_nonneg q)
    (mul_nonneg (HotApplication.realBound_pos q).le (H_nonneg q v)) v 0 hv

variable {X : Type*} [MeasurableSpace X]

theorem measurable_density {f : X × Velocity → ℝ} (hf : Measurable f) (q : ℝ) :
    Measurable (density q f) := ((measurable_H q).comp measurable_snd).mul hf

theorem measurable_gain {f : X × Velocity → ℝ} (hf : Measurable f) (q b : ℝ) :
    Measurable (gain q b f) :=
  Measurable.ite ((measurableSet_good q).preimage measurable_snd)
    ((KineticCollisionNullSets.measurable_gain (measurable_density hf q) b).div
      ((measurable_H q).comp measurable_snd)) measurable_const

theorem measurable_frequency {f : X × Velocity → ℝ} (hf : Measurable f) (q b : ℝ) :
    Measurable (frequency q b f) :=
  KineticCollisionNullSets.measurable_frequency (measurable_density hf q) b

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Pointwise weighted gain bounds off the fixed exceptional set -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

theorem actual_gain_bound {q A : ℝ} {v : Velocity} (hv : v ∈ good q)
    {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (hfB : ∀ w, f w ≤ A * H q w) (b : ℝ) :
    CollisionCutoff.gain b f v ≤ A^2 * HotApplication.realBound q * H q v := by
  have hi := GainOrder.integrable_const_mul A v (integrable_H_gain hv)
  calc
    _ ≤ BoltzmannNonuniqueness.gain (fun p => f p.2) 0 v :=
      CollisionCutoff.gain_le b hfm hf v 0 (GainOrder.integrable_of_le hfm hf hfB v hi)
    _ ≤ BoltzmannNonuniqueness.gain (fun p => A * H q p.2) 0 v :=
      GainOrder.gain_mono hfm hf hfB v 0 hi
    _ = A^2 * BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v :=
      GainOrder.gain_const_mul A (H q) v 0
    _ ≤ A^2 * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (H_gain_bound hv) (sq_nonneg A)
    _ = _ := by ring

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem gain_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (q b : ℝ) (p : X × Velocity) :
    0 ≤ gain q b f p := by
  unfold gain
  split_ifs
  · apply div_nonneg _ (H_nonneg _ _)
    apply integral_nonneg
    intro w
    exact mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _)
      (mul_nonneg (H_nonneg _ _) (hf _))) (mul_nonneg (H_nonneg _ _) (hf _))
  · exact le_rfl

theorem gain_bound {q A : ℝ} (_hA : 0 ≤ A) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (b : ℝ) (p : X × Velocity) :
    gain q b f p ≤ A^2 * HotApplication.realBound q := by
  unfold gain
  split_ifs with hv
  · apply (div_le_iff₀ (H_pos q p.2)).mpr
    apply actual_gain_bound hv
      ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
      (fun w => mul_nonneg (H_nonneg _ _) (hf _).1)
    intro w
    exact (mul_le_mul_of_nonneg_left (hf _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _)
  · exact mul_nonneg (sq_nonneg A) (HotApplication.realBound_pos q).le

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Loss estimates and the collision meaning of weighted representatives -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem density_bounds {q A : ℝ} {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (p : X × Velocity) :
    0 ≤ density q f p ∧ density q f p ≤ A * H q p.2 :=
  ⟨mul_nonneg (H_nonneg _ _) (hf p).1,
    (mul_le_mul_of_nonneg_left (hf p).2 (H_nonneg _ _)).trans_eq (mul_comm _ _)⟩

omit [MeasurableSpace X] in
theorem frequency_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (q b : ℝ) (p : X × Velocity) : 0 ≤ frequency q b f p :=
  CutoffLipschitz.frequency_nonneg (fun _ => mul_nonneg (H_nonneg _ _) (hf _)) b p.2

theorem frequency_bound {q A b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A)
    (p : X × Velocity) : frequency q b f p ≤ A * CutoffLipschitz.frequencyConstant q b :=
  CutoffLipschitz.frequency_bound hq hb
    ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
    (fun w => (density_bounds hf (p.1,w)).1) (fun w => (density_bounds hf (p.1,w)).2) p.2

omit [MeasurableSpace X] in
theorem physical_gain_eq {q b : ℝ} (f : X × Velocity → ℝ) {p : X × Velocity}
    (hp : p.2 ∈ good q) : H q p.2 * gain q b f p =
      KineticCollisionNullSets.gain b (density q f) p := by
  rw [gain, ite_eq_left hp]
  field_simp [(H_pos q p.2).ne']

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Bounded positive source for the H-weighted local equation -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem measurable_source {f : X × Velocity → ℝ} (hf : Measurable f) (q b L : ℝ) :
    Measurable (source q b L f) :=
  (measurable_gain hf q b).add ((measurable_const.sub (measurable_frequency hf q b)).mul hf)

theorem source_bounds {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : R * CutoffLipschitz.frequencyConstant q b ≤ L)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R)
    (p : X × Velocity) :
    0 ≤ source q b L f p ∧ source q b L f p ≤ HotApplication.realBound q * R^2 + L*R := by
  have hν := frequency_nonneg (fun p => (hf p).1) q b p
  have hνB := frequency_bound hq hb hfm hf p
  have hLp : 0 ≤ L := (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)).trans hL
  constructor
  · exact add_nonneg (gain_nonneg (fun p => (hf p).1) q b p)
      (mul_nonneg (sub_nonneg.mpr (hνB.trans hL)) (hf p).1)
  · have hg := gain_bound (q := q) hR hfm hf b p
    have hl : (L - frequency q b f p) * f p ≤ L*R :=
      (mul_le_mul_of_nonneg_right (sub_le_self _ hν) (hf p).1).trans
        (mul_le_mul_of_nonneg_left (hf p).2 hLp)
    unfold source
    nlinarith only [hg,hl]

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Cancellation of artificial damping in the physical collision equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem physical_source_eq {q b L : ℝ} (f : X × Velocity → ℝ) {p : X × Velocity}
    (hp : p.2 ∈ good q) :
    H q p.2 * (source q b L f p-L*f p) =
      CollisionCompactness.collisionSource b (density q f) p := by
  have hg := physical_gain_eq (b := b) f hp
  unfold source CollisionCompactness.collisionSource frequency
  rw [← hg]
  unfold density
  ring

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetSolutions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive local iteration in the manuscript's singular weighted norm -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem measurable_forcing {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) (q b L : ℝ) :
    Measurable (forcing q b L f) :=
  (HotRepresentative.measurable_source (GaussianLocal.measurable_state hf) q b L).comp (by fun_prop)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Spatial covariance of the constructed weighted cold solutions -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.WeightedTranslation

theorem measurable_shift (y : Space) : Measurable (shift y) := by
  unfold shift
  fun_prop

end BoltzmannNonuniqueness.WeightedTranslation

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

theorem WeakL1Converges.add {μ : Measure X} {f k : ℕ → X → ℝ} {g h : X → ℝ}
    (hf : WeakL1Converges μ f g) (hk : WeakL1Converges μ k h)
    (hfi : ∀ n, Integrable (f n) μ) (hki : ∀ n, Integrable (k n) μ) :
    WeakL1Converges μ (fun n x => f n x+k n x) (fun x => g x+h x) := by
  refine ⟨hf.1.add hk.1,hf.2.1.add hk.2.1,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have hm (u : X → ℝ) (hu : Integrable u μ) : Integrable (fun x => ψ x*u x) μ :=
    hu.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have he (u v : X → ℝ) (hu : Integrable u μ) (hv : Integrable v μ) :
      (∫ x, ψ x*(u x+v x) ∂μ) = (∫ x, ψ x*u x ∂μ)+(∫ x, ψ x*v x ∂μ) := by
    simp_rw [mul_add]
    exact integral_add (hm u hu) (hm v hv)
  simp_rw [he _ _ (hfi _) (hki _),he _ _ hf.2.1 hk.2.1]
  exact (hf.2.2 ψ hψ ⟨C,hC⟩).add (hk.2.2 ψ hψ ⟨C,hC⟩)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Recovering a weighted weak limit from its unweighted density -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem identify_weighted_weak_limit {μ : Measure X} {f : ℕ → X → ℝ} {g G w : X → ℝ}
    (hg : WeakL1Converges μ f g)
    (hG : WeakL1Converges μ (fun n x => w x*f n x) G)
    (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) :
    G =ᵐ[μ] (fun x => w x*g x) := by
  have hwpos (x) : 0 < w x := lt_of_lt_of_le zero_lt_one (hw1 x)
  have hinv : ∀ x, |(w x)⁻¹| ≤ 1 := by
    intro x
    rw [abs_of_pos (inv_pos.mpr (hwpos x))]
    exact inv_le_one_of_one_le₀ (hw1 x)
  have hback := hG.bounded_mul hw.inv 1 hinv
  change WeakL1Converges μ (fun n x => (w x)⁻¹*(w x*f n x))
    (fun x => (w x)⁻¹*G x) at hback
  have he : (fun n x => (w x)⁻¹*(w x*f n x)) = f := by
    funext n x
    rw [← mul_assoc,inv_mul_cancel₀ (hwpos x).ne',one_mul]
  rw [he] at hback
  have heq := hg.unique hback
  filter_upwards [heq] with x hx
  change g x = (w x)⁻¹*G x at hx
  rw [hx,← mul_assoc,mul_inv_cancel₀ (hwpos x).ne',one_mul]

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_PeriodicJetFamilies
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countably labeled periodic copies of the finite cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem measurable_color (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : JetLattice.Label) :
    Measurable (color s₀ η K α γ d₀ q N i) := by
  unfold color
  split_ifs
  · exact ((JetDatum.term_measurable s₀ η K α γ d₀ _).comp (measurable_shift _)).div
      ((ChartKernel.measurable_H q).comp measurable_snd)
  · exact measurable_const

theorem measurable_seed (s₀ η K α γ d₀ q : ℝ) (N : ℕ) : Measurable (seed s₀ η K α γ d₀ q N) :=
  Measurable.tsum (measurable_color s₀ η K α γ d₀ q N)

private theorem in_enlargement {s₀ η K α γ d₀ q : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) {i : JetLattice.Label} {p : JetPrototype.Phase}
    (hp : color s₀ η K α γ d₀ q N i p ≠ 0) :
    PlaneChart.join p.1.1 p.1.2 ∈ JetLattice.spatialEnlargement s₀ η 0 i := by
  have hi : i.annulus < N := by
    by_contra h
    exact hp (by simp only [color,ite_eq_right h])
  have hn : JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement i.lattice) p) ≠ 0 := by
    intro h
    exact hp (by simp only [color,ite_eq_left hi,h,zero_div])
  have hsp := JetSupport.initial_spatial_support η K α γ
    (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) i.positive hn
  constructor
  · rw [PlaneChart.transverse_join]
    apply Metric.mem_cthickening_of_dist_le _ _ _ _ hsp.1
    simpa [shift,displacement,jetScale] using (enlargementWidth_pos hη
      (DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1))).le
  · have hax : |p.1.2-JetLattice.axialShift i.lattice| < 1/8 := hsp.2
    change |axial (PlaneChart.join p.1.1 p.1.2)-JetLattice.axialShift i.lattice| ≤ _
    rw [PlaneChart.axial_join]
    linarith

theorem color_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ)
    (p : JetPrototype.Phase) (i j : JetLattice.Label) (hij : i ≠ j)
    (hi : color s₀ η K α γ d₀ q N i p ≠ 0) : color s₀ η K α γ d₀ q N j p = 0 := by
  by_contra hj
  exact hij (JetLattice.common_point_label hs₀ hsmax hη hηmax (by norm_num : (0:ℝ) ≤ 1/32)
    (in_enlargement hs₀ hη hi) (in_enlargement hs₀ hη hj))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The periodic finite cold seed equals the manuscript datum in the central cube -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

private theorem integer_zero_of_close {x : ℝ} {n : ℤ}
    (hx : x ∈ TorusChart.interval) (hn : |x-(n:ℝ)| < 1/4) : n = 0 := by
  by_contra h
  have hi := JetLattice.integer_distance h
  have ha : |x| ≤ 1/2 := abs_le.mpr ⟨hx.1.le,hx.2⟩
  have ht := abs_add_le ((n:ℝ)-x) x
  rw [sub_add_cancel,abs_sub_comm] at ht
  simp only [Int.cast_zero,sub_zero] at hi
  linarith

theorem term_shift_lattice_zero {s₀ η K α γ d₀ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    {i : JetDatum.Index} {n : JetLattice.Lattice} {y : Velocity} {v : Velocity}
    (hy : y ∈ TorusChart.cube)
    (hp : JetDatum.term s₀ η K α γ d₀ i
      (shift (displacement n) (JetPeriodicDatum.spatialMap y,v)) ≠ 0) : n = 0 := by
  have hsp := JetSupport.initial_spatial_support η K α γ _ _ i.2 hp
  have hnorm : ‖(transverse y-JetLattice.transverseShift n)‖ < s₀ := by
    have hh := hsp.1.1.2
    change ‖transverse y-JetLattice.transverseShift n‖ <
      Real.exp η*jetScale s₀ η i.1-gapCoefficient η*jetScale s₀ η i.1^2 at hh
    have hg : 0 ≤ gapCoefficient η*jetScale s₀ η i.1^2 :=
      mul_nonneg (gapCoefficient_pos hη).le (sq_nonneg _)
    rw [outerRadius_eq] at hh
    have hb := scale_antitone hs₀.le hη.le (Nat.zero_le i.1)
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at hb
    linarith
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · apply integer_zero_of_close (hy (Fin.last 2))
    have hz : |y (Fin.last 2)-(n (Fin.last 2):ℝ)| < 1/8 := hsp.2
    linarith
  · apply integer_zero_of_close (hy j.castSucc)
    have hc := PiLp.norm_apply_le (transverse y-JetLattice.transverseShift n) j
    change ‖y j.castSucc-(n j.castSucc:ℝ)‖ ≤ _ at hc
    rw [Real.norm_eq_abs] at hc
    exact (hc.trans_lt hnorm).trans_le (by linarith)

theorem color_central {s₀ η K α γ d₀ q : ℝ} (N : ℕ) (i : JetDatum.Index)
    (p : JetPrototype.Phase) :
    color s₀ η K α γ d₀ q N ⟨i.1,i.2,0⟩ p =
      (if i.1 < N then JetDatum.term s₀ η K α γ d₀ i p else 0)/H q p.2 := by
  have hz : displacement 0 = 0 := by
    apply Prod.ext
    · ext j; simp [displacement,JetLattice.transverseShift]
    · simp [displacement,JetLattice.axialShift]
  have hshift : shift (displacement 0) p = p := by rw [hz]; apply Prod.ext <;> simp [shift]
  simp only [color,hshift]
  split_ifs <;> simp

theorem seed_on_cube {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ)
    {y : Velocity} (hy : y ∈ TorusChart.cube) (v : Velocity) :
    seed s₀ η K α γ d₀ q N (JetPeriodicDatum.spatialMap y,v) =
      JetTruncation.truncated s₀ η K α γ d₀ N (JetPeriodicDatum.spatialMap y,v)/H q v := by
  classical
  let p : JetPrototype.Phase := (JetPeriodicDatum.spatialMap y,v)
  have hlat (i : JetLattice.Label) (hi : color s₀ η K α γ d₀ q N i p ≠ 0) : i.lattice = 0 := by
    have hN : i.annulus < N := by
      by_contra hn
      exact hi (by simp only [color,ite_eq_right hn])
    have ht : JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
        (shift (displacement i.lattice) p) ≠ 0 := by
      intro ht
      exact hi (by simp only [color,ite_eq_left hN,ht,zero_div])
    exact term_shift_lattice_zero hs₀ hsmax hη hy ht
  by_cases hex : ∃ j : JetDatum.Index, j.1 < N ∧ JetDatum.term s₀ η K α γ d₀ j p ≠ 0
  · obtain ⟨j,hjN,hj⟩ := hex
    let i : JetLattice.Label := ⟨j.1,j.2,0⟩
    have hi : color s₀ η K α γ d₀ q N i p ≠ 0 := by
      rw [color_central,ite_eq_left hjN]
      exact div_ne_zero hj (H_pos q v).ne'
    have hseed : seed s₀ η K α γ d₀ q N p = color s₀ η K α γ d₀ q N i p :=
      tsum_eq_single i (fun k hk => color_disjoint hs₀ hsmax hη hηmax K α γ d₀ q N p i k hk.symm hi)
    have htrunc : JetTruncation.truncated s₀ η K α γ d₀ N p = JetDatum.term s₀ η K α γ d₀ j p := by
      unfold JetTruncation.truncated
      rw [tsum_eq_single j]
      · exact ite_eq_left hjN
      · intro k hk
        rw [JetDatum.term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p j k hk.symm hj]
        simp
    change seed s₀ η K α γ d₀ q N p = JetTruncation.truncated s₀ η K α γ d₀ N p/H q v
    rw [hseed,htrunc,color_central,ite_eq_left hjN]
  · have htrunc : JetTruncation.truncated s₀ η K α γ d₀ N p = 0 := by
      calc
        _ = ∑' j : JetDatum.Index, (0:ℝ) := tsum_congr (fun j => ?_)
        _ = 0 := tsum_zero
      by_cases hjN : j.1 < N
      · have hj : JetDatum.term s₀ η K α γ d₀ j p = 0 := by
          by_contra hj
          exact hex ⟨j,hjN,hj⟩
        rw [ite_eq_left hjN,hj]
      · exact ite_eq_right hjN
    have hseed : seed s₀ η K α γ d₀ q N p = 0 := by
      calc
        _ = ∑' i : JetLattice.Label, (0:ℝ) := tsum_congr (fun i => ?_)
        _ = 0 := tsum_zero
      by_contra hi
      have hl := hlat i hi
      have he : i = ⟨i.annulus,i.positive,0⟩ := by cases i; simp_all
      rw [he] at hi
      rw [color_central N (i.annulus,i.positive) p] at hi
      by_cases hN : i.annulus < N
      · rw [ite_eq_left hN] at hi
        have ht : JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive) p ≠ 0 :=
          fun h => hi (by rw [h,zero_div])
        exact hex ⟨(i.annulus,i.positive),hN,ht⟩
      · exact hi (by rw [ite_eq_right hN,zero_div])
    change seed s₀ η K α γ d₀ q N p = JetTruncation.truncated s₀ η K α γ d₀ N p/H q v
    rw [hseed,htrunc,zero_div]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotSeedCoreLower
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A localized periodic thermal seed, normalized in the singular weighted norm -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem bound_pos : 0 < bound := by
  unfold bound
  exact mul_pos (mul_pos (sq_pos_of_pos JetThermalKernel.bound_pos) (Real.exp_pos _)) tiltConstant_pos

theorem measurable_centered : Measurable centered :=
  ((measurable_id.add_const (1/2)).fract).sub_const (1/2)

theorem measurable_centeredSpace : Measurable centeredSpace := by
  apply Measurable.prodMk
  · apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp
    exact Measurable.of_eval (fun i => measurable_centered.comp
      (show Measurable (fun x : Space => x.1 i) from by fun_prop))
  · exact measurable_centered.comp measurable_snd

theorem measurable_raw (q δ : ℝ) : Measurable (raw q δ) := by
  have hjoin : Measurable (fun x : Space => PlaneChart.join x.1 x.2) :=
    split.symm.measurable.comp (measurable_snd.prodMk measurable_fst)
  exact (JetThermalKernel.J_smooth.continuous.measurable.comp
    ((hjoin.comp (measurable_centeredSpace.comp measurable_fst)).const_smul δ⁻¹)).mul
    ((JetThermalKernel.J_smooth.continuous.measurable.comp measurable_snd).div
      ((ChartKernel.measurable_H q).comp measurable_snd))

theorem raw_nonneg (q δ : ℝ) (p : JetPrototype.Phase) : 0 ≤ raw q δ p :=
  mul_nonneg (JetThermalKernel.J_nonneg _) (div_nonneg (JetThermalKernel.J_nonneg _) (H_nonneg _ _))

theorem velocity_bound (q : ℝ) (v : Velocity) :
    JetThermalKernel.J v/H q v ≤ JetThermalKernel.bound*Real.exp 2*tiltConstant := by
  by_cases hv : 1 ≤ ‖v‖
  · rw [JetThermalKernel.J_zero hv,zero_div]
    exact mul_nonneg (mul_nonneg JetThermalKernel.bound_pos.le (Real.exp_pos _).le) tiltConstant_pos.le
  · have hv2 : ‖v‖^2 ≤ 1 := by nlinarith [norm_nonneg v,lt_of_not_ge hv]
    have he : 1 ≤ Real.exp 2*Real.exp (-2*‖v‖^2) := by
      rw [← Real.exp_add,← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    apply (div_le_iff₀ (H_pos q v)).mpr
    calc
      _ ≤ JetThermalKernel.bound := JetThermalKernel.J_le v
      _ ≤ JetThermalKernel.bound*(Real.exp 2*Real.exp (-2*‖v‖^2)) :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left he JetThermalKernel.bound_pos.le
      _ ≤ JetThermalKernel.bound*(Real.exp 2*(tiltConstant*H q v)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q v) (Real.exp_pos _).le)
          JetThermalKernel.bound_pos.le
      _ = _ := by ring

theorem raw_le (q δ : ℝ) (p : JetPrototype.Phase) : raw q δ p ≤ bound := by
  unfold raw bound
  have h := mul_le_mul
    (JetThermalKernel.J_le (δ⁻¹ • PlaneChart.join (centeredSpace p.1).1 (centeredSpace p.1).2))
    (velocity_bound q p.2)
    (div_nonneg (JetThermalKernel.J_nonneg _) (H_nonneg _ _)) JetThermalKernel.bound_pos.le
  exact h.trans_eq (by ring)

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # The localized thermal seed has positive essential weighted norm -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_pos_of_positive_set {f : JetPrototype.Phase → ℝ} {R : ℝ}
    (hfm : Measurable f) (hb : ∀ p, |f p| ≤ R) {s : Set JetPrototype.Phase}
    (hs : FlightMeasure.phaseVolume s ≠ 0) (hf : ∀ p ∈ s, 0 < f p) : 0 < size f := by
  obtain ⟨p,hp,hbound⟩ := exists_mem_of_measure_ne_zero_of_ae hs
    (ae_restrict_of_ae (ae_abs_le_size hfm hb))
  exact (hf p hp).trans_le ((le_abs_self _).trans hbound)

end BoltzmannNonuniqueness.PhaseEssSup

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem centered_eq {x : ℝ} (hx : |x| < 1/2) : centered x = x := by
  have h := abs_lt.mp hx
  unfold centered
  rw [Int.fract_eq_self.mpr ⟨by linarith [h.1],by linarith [h.2]⟩]
  ring

theorem centeredSpace_eq {x : Space} (hx : ‖x‖ < 1/2) : centeredSpace x = x := by
  apply Prod.ext
  · ext i
    apply centered_eq
    exact (show |x.1 i| ≤ ‖x.1‖ from by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x.1 i).trans_lt
      ((norm_fst_le x).trans_lt hx)
  · apply centered_eq
    exact (show |x.2| ≤ ‖x‖ from by simpa only [Real.norm_eq_abs] using norm_snd_le x).trans_lt hx

theorem J_pos {v : Velocity} (hv : ‖v‖ < 1) : 0 < JetThermalKernel.J v := by
  have hn : JetThermalKernel.J v ≠ 0 := by
    change v ∈ Function.support JetThermalKernel.J
    rw [JetThermalKernel.J_support]
    simpa only [mem_ball,dist_zero_right] using hv
  exact lt_of_le_of_ne (JetThermalKernel.J_nonneg v) hn.symm

theorem raw_pos {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ)
    {p : JetPrototype.Phase} (hx : ‖p.1‖ < δ/4) (hv : ‖p.2‖ < 1/2) : 0 < raw q δ p := by
  have hc : centeredSpace p.1 = p.1 := centeredSpace_eq (by linarith)
  have hu : ‖p.1.1‖ < δ/4 := (norm_fst_le p.1).trans_lt hx
  have hz : |p.1.2| < δ/4 := by simpa only [Real.norm_eq_abs] using (norm_snd_le p.1).trans_lt hx
  have hj : ‖PlaneChart.join p.1.1 p.1.2‖ < δ := by
    have he := PlaneChart.norm_join_sq p.1.1 p.1.2
    have hsq := sq_abs p.1.2
    nlinarith [norm_nonneg p.1.1,norm_nonneg (PlaneChart.join p.1.1 p.1.2),abs_nonneg p.1.2]
  have harg : ‖δ⁻¹ • PlaneChart.join p.1.1 p.1.2‖ < 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]
    exact (inv_mul_lt_one₀ hδ).mpr hj
  unfold raw
  rw [hc]
  exact mul_pos (J_pos harg) (div_pos (J_pos (by linarith)) (H_pos q p.2))

theorem raw_size_pos {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    0 < PhaseEssSup.size (raw q δ) := by
  let s : Set JetPrototype.Phase := ball (0 : Space) (δ/4) ×ˢ ball (0 : Velocity) (1/2)
  have hs : FlightMeasure.phaseVolume s ≠ 0 := by
    change ((volume : Measure Space).prod (volume : Measure Velocity))
      (ball (0 : Space) (δ/4) ×ˢ ball (0 : Velocity) (1/2)) ≠ 0
    rw [Measure.prod_prod]
    exact mul_ne_zero (measure_ball_pos volume (0 : Space) (by linarith)).ne'
      (measure_ball_pos volume (0 : Velocity) (by norm_num : (0:ℝ) < 1/2)).ne'
  apply PhaseEssSup.size_pos_of_positive_set (measurable_raw q δ)
    (fun p => by rw [abs_of_nonneg (raw_nonneg q δ p)]; exact raw_le q δ p) hs
  intro p hp
  exact raw_pos hδ hδmax q (by simpa only [mem_ball,dist_zero_right] using hp.1)
    (by simpa only [mem_ball,dist_zero_right] using hp.2)

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # The normalized periodic hot seed has the data required by cap selection -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem normalized_measurable (q δ : ℝ) : Measurable (normalized q δ) :=
  (measurable_raw q δ).const_mul _

theorem normalized_bounds {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ p, 0 ≤ normalized q δ p ∧ normalized q δ p ≤ M := by
  have hs := raw_size_pos hδ hδmax q
  let c := δ/PhaseEssSup.size (raw q δ)
  have hc : 0 < c := div_pos hδ hs
  refine ⟨c*bound,mul_pos hc bound_pos,?_⟩
  intro p
  exact ⟨mul_nonneg hc.le (raw_nonneg q δ p),mul_le_mul_of_nonneg_left (raw_le q δ p) hc.le⟩

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # Scale-independent amplitude bound for the localized thermal seed -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem J_eq_bound {v : Velocity} (hv : ‖v‖ ≤ 1/2) :
    JetThermalKernel.J v = JetThermalKernel.bound := by
  unfold JetThermalKernel.J ContDiffBump.normed JetThermalKernel.bound
  rw [JetThermalKernel.bump.one_of_mem_closedBall (by
    simpa only [mem_closedBall,dist_zero_right,JetThermalKernel.bump] using hv),one_div]

theorem velocityCore_open : IsOpen velocityCore := by
  have hc : Continuous transverse := by
    unfold transverse
    fun_prop
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const hc.norm)

theorem velocityCore_nonempty : velocityCore.Nonempty := by
  let u : Transverse := PiLp.single 2 (0 : Fin 2) (1/4 : ℝ)
  have hu : ‖u‖ = 1/4 := by simp [u]
  have hj : ‖PlaneChart.join u 0‖ = 1/4 := by
    have h := PlaneChart.norm_join_sq u 0
    rw [hu] at h
    nlinarith [norm_nonneg (PlaneChart.join u 0)]
  refine ⟨PlaneChart.join u 0,?_⟩
  change ‖PlaneChart.join u 0‖ < 1/2 ∧ 1/8 < ‖transverse (PlaneChart.join u 0)‖
  rw [PlaneChart.transverse_join,hu,hj]
  norm_num

theorem velocityBound_pos (q : ℝ) : 0 < velocityBound q := by
  unfold velocityBound
  positivity

theorem H_le_velocityBound {q : ℝ} (hq : 0 ≤ q) {v : Velocity}
    (hv : v ∈ velocityCore) : H q v ≤ velocityBound q := by
  have he : Real.exp (-‖v‖^2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hp : (1+‖v‖^2)^(-50 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖v‖]) (by norm_num)
  have hr : ‖transverse v‖^(-q) ≤ (1/8 : ℝ)^(-q) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hv.2.le (neg_nonpos.mpr hq)
  unfold H singularity velocityBound
  have hm : Real.exp (-‖v‖^2)*(1+‖v‖^2)^(-50 : ℝ) ≤ 1 := by
    simpa using mul_le_mul he hp (Real.rpow_nonneg (by positivity) _) (by norm_num : (0:ℝ) ≤ 1)
  exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans (by linarith)

theorem normLower_pos (q : ℝ) : 0 < normLower q :=
  div_pos (sq_pos_of_pos JetThermalKernel.bound_pos) (velocityBound_pos q)

theorem spatial_core {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) {x : Space}
    (hx : ‖x‖ < δ/8) :
    JetThermalKernel.J (δ⁻¹ • PlaneChart.join (centeredSpace x).1 (centeredSpace x).2) =
      JetThermalKernel.bound := by
  have hc : centeredSpace x = x := centeredSpace_eq (by linarith)
  rw [hc]
  apply J_eq_bound
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]
  apply (inv_mul_le_iff₀ hδ).mpr
  have hu : ‖x.1‖ < δ/8 := (norm_fst_le x).trans_lt hx
  have hz : |x.2| < δ/8 := by simpa only [Real.norm_eq_abs] using (norm_snd_le x).trans_lt hx
  have he := PlaneChart.norm_join_sq x.1 x.2
  nlinarith [norm_nonneg x.1,norm_nonneg (PlaneChart.join x.1 x.2),sq_abs x.2,abs_nonneg x.2]

theorem raw_ge_normLower {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    {p : JetPrototype.Phase} (hx : ‖p.1‖ < δ/8) (hv : p.2 ∈ velocityCore) :
    normLower q ≤ raw q δ p := by
  unfold raw
  rw [spatial_core hδ hδmax hx,J_eq_bound hv.1.le]
  unfold normLower
  rw [sq, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left JetThermalKernel.bound_pos.le (H_pos q p.2)
      (H_le_velocityBound hq hv)) JetThermalKernel.bound_pos.le

theorem normLower_le_size {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    normLower q ≤ PhaseEssSup.size (raw q δ) := by
  let s : Set JetPrototype.Phase := ball (0 : Space) (δ/8) ×ˢ velocityCore
  have hs : FlightMeasure.phaseVolume s ≠ 0 := by
    change ((volume : Measure Space).prod (volume : Measure Velocity))
      (ball (0 : Space) (δ/8) ×ˢ velocityCore) ≠ 0
    rw [Measure.prod_prod]
    exact mul_ne_zero (measure_ball_pos volume (0 : Space) (by linarith)).ne'
      (velocityCore_open.measure_ne_zero volume velocityCore_nonempty)
  obtain ⟨p,hp,hbound⟩ := exists_mem_of_measure_ne_zero_of_ae hs
    (ae_restrict_of_ae (PhaseEssSup.ae_abs_le_size (measurable_raw q δ)
      (fun p => by rw [abs_of_nonneg (raw_nonneg q δ p)]; exact raw_le q δ p)))
  exact (raw_ge_normLower hq hδ hδmax
    (by simpa only [mem_ball,dist_zero_right] using hp.1) hp.2).trans
      ((le_abs_self _).trans hbound)

theorem normalized_uniform_bound {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (p : JetPrototype.Phase) :
    normalized q δ p ≤ (bound/normLower q)*δ := by
  have hs := normLower_le_size hq hδ hδmax
  have hn := normLower_pos q
  have hsize := hn.trans_le hs
  unfold normalized
  calc
    _ ≤ (δ/normLower q)*bound := mul_le_mul
      (div_le_div_of_nonneg_left hδ.le hn hs) (raw_le q δ p) (raw_nonneg q δ p)
      (div_nonneg hδ.le hn.le)
    _ = _ := by ring

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # Vanishing of the actual hot seed on the spatial torus -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem periodicDensity_measurable (q δ : ℝ) : Measurable (periodicDensity q δ) :=
  ((normalized_measurable q δ).comp
    (JetPeriodicDatum.phaseMap_measurePreserving.measurable.comp
      TorusChart.phase_measurePreserving.measurable)).mul
    ((ChartKernel.measurable_H q).comp measurable_snd)

theorem periodicDensity_nonneg {q δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (p : Phase) :
    0 ≤ periodicDensity q δ p := by
  obtain ⟨M,hM,hb⟩ := normalized_bounds hδ hδmax q
  exact mul_nonneg (hb _).1 (H_nonneg q p.2)

theorem periodicDensity_bound {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hδmax : δ ≤ 1)
    (p : Phase) : periodicDensity q δ p ≤ (bound/normLower q)*δ*H q p.2 :=
  mul_le_mul_of_nonneg_right (normalized_uniform_bound hq hδ hδmax _) (H_nonneg _ _)

theorem integrable_weight_torus {q : ℝ} (hq : q < 2) :
    Integrable (fun p : Phase => H q p.2) := by
  rw [Measure.volume_eq_prod]
  simpa only [one_mul] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : Position => (1 : ℝ))).mul_prod (integrable_H hq)

theorem periodicDensity_integrable {q δ : ℝ} (hq : 0 ≤ q) (hqmax : q < 2)
    (hδ : 0 < δ) (hδmax : δ ≤ 1) : Integrable (periodicDensity q δ) := by
  apply ((integrable_weight_torus hqmax).const_mul ((bound/normLower q)*δ)).mono'
    (periodicDensity_measurable q δ).aestronglyMeasurable
  exact ae_of_all _ (fun p => by
    rw [Real.norm_of_nonneg (periodicDensity_nonneg hδ hδmax p)]
    exact periodicDensity_bound hq hδ hδmax p)

end BoltzmannNonuniqueness.HotSeedProfile

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetFamilyBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual periodic shooting data converge to the common cold datum in L¹ -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetPeriodicDatum

theorem measurable_pullback {f : JetPrototype.Phase → ℝ} (hf : Measurable f) :
    Measurable (pullback f) :=
  hf.comp (phaseMap_measurePreserving.measurable.comp TorusChart.phase_measurePreserving.measurable)

theorem truncated_integrable {s₀ η K γ d₀ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) (N : ℕ) :
    Integrable (truncated s₀ η K α γ d₀ N) := by
  have hi := integrable_pullback (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α)
  apply hi.mono' (measurable_pullback (JetTruncation.truncated_measurable s₀ η K α γ d₀ N)).aestronglyMeasurable
  filter_upwards [] with p
  have h := JetTruncation.truncated_eq_or_zero hs₀ hsmax hη hηmax K α γ d₀ N
    (phaseMap (TorusChart.phaseRepresentative p))
  rcases h with h | h
  · change ‖JetTruncation.truncated _ _ _ _ _ _ _ _‖ ≤ _
    rw [h,Real.norm_of_nonneg (JetDatumMoments.datum_nonneg hs₀ hK hd₀.le η α γ _)]
    exact le_rfl
  · change ‖JetTruncation.truncated _ _ _ _ _ _ _ _‖ ≤ _
    rw [h,norm_zero]
    exact JetDatumMoments.datum_nonneg hs₀ hK hd₀.le η α γ _

end BoltzmannNonuniqueness.JetPeriodicDatum

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem periodicInitial_eq {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ) (ell : ℝ)
    (p : Phase) :
    periodicInitial s₀ η K α γ d₀ q N ell p =
      JetPeriodicDatum.truncated s₀ η K α γ d₀ N p+
        ell*HotSeedProfile.periodicDensity q (DatumBounds.scale s₀ η (N+1)) p := by
  have he := seed_on_cube hs₀ hsmax hη hηmax K α γ d₀ q N
    (TorusChart.representative_mem p.1) p.2
  change (seed s₀ η K α γ d₀ q N (JetPeriodicDatum.spatialMap (TorusChart.representative p.1),p.2)+
    ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1))
      (JetPeriodicDatum.spatialMap (TorusChart.representative p.1),p.2))*H q p.2 = _
  rw [he,add_mul,div_mul_cancel₀ _ (H_pos q p.2).ne']
  simp only [JetPeriodicDatum.truncated,JetPeriodicDatum.pullback,HotSeedProfile.periodicDensity,
    JetPeriodicDatum.phaseMap,TorusChart.phaseRepresentative]
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildCharacteristics
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The weak characteristic equation of the constructed mild states -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_along_flight {T t : ℝ} (ht : t ∈ Icc 0 T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ)
    (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (t,JetBarrier.flight t p) =
      TransportPrimitive.damped L (f₀ p) (fun r => g (r,JetBarrier.flight r p)) t := by
  rw [TransportPrimitive.damped_eq]
  unfold value
  rw [GaussianLocal.time_eq ht,JetFreeTransport.neg_flight]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [JetFreeTransport.flight_add,sub_add_cancel]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Characteristic localization of bounded measurable mild solutions -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem characteristic_ae {T L : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p))) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (fun t => F (t,JetBarrier.flight t p)) =ᵐ[volume.restrict (Icc 0 T)]
        (fun t => TransportPrimitive.damped L (f₀ p)
          (fun r => g (r,JetBarrier.flight r p)) t) := by
  let A : ℝ × JetPrototype.Phase → ℝ := fun z => F (z.1,JetBarrier.flight z.1 z.2)
  let B : ℝ × JetPrototype.Phase → ℝ := fun z =>
    value T L JetBarrier.flight f₀ g (z.1,JetBarrier.flight z.1 z.2)
  have hflow : Measurable (fun z : ℝ × JetPrototype.Phase =>
      (z.1,JetBarrier.flight z.1 z.2)) :=
    measurable_fst.prodMk GaussianLocal.measurable_flight
  have hAm : Measurable A := hFm.comp hflow
  have hBm : Measurable B :=
    (measurable_value hT GaussianLocal.measurable_flight hf₀ hgm).comp hflow
  have hall : A =ᵐ[(volume.restrict (Icc 0 T)).prod FlightMeasure.phaseVolume] B := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hAm hBm)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (FlightMeasure.flight_measurePreserving t).quasiMeasurePreserving.ae (hmild t ht)
  have hp := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume)
      (ν := volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae hall)
  filter_upwards [hp] with p hpe
  filter_upwards [hpe,ae_restrict_mem measurableSet_Icc] with t ht htm
  exact ht.trans (value_along_flight htm L f₀ g p)

/-- The damping parameter of the iteration cancels, leaving the physical
source `g-L*F` plus the differentiated cutoff in a unit-damped formula. -/
theorem localized_characteristic {T L S : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ z, |g z| ≤ S)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p)))
    (χ χ' : JetPrototype.Phase → ℝ → ℝ)
    (hχ : ∀ p, ContinuousOn (χ p) (Icc 0 T))
    (hχ' : ∀ p, ContinuousOn (χ' p) (Icc 0 T))
    (hdχ : ∀ p t, t ∈ Icc 0 T → HasDerivAt (χ p) (χ' p t) t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      χ p T*F (T,JetBarrier.flight T p) = Real.exp (-T)*χ p 0*f₀ p +
        ∫ t in 0..T, Real.exp (-(T-t)) *
          (χ p t*(g (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p)) +
            (χ' p t+χ p t)*F (t,JetBarrier.flight t p)) := by
  have hp := characteristic_ae hT hf₀ hFm hgm hmild
  have ht := (FlightMeasure.flight_measurePreserving T).quasiMeasurePreserving.ae
    (hmild T ⟨hT,le_rfl⟩)
  filter_upwards [hp,ht] with p hpe hpend
  have hgi : IntervalIntegrable (fun t => g (t,JetBarrier.flight t p)) volume 0 T := by
    apply (intervalIntegrable_const (c := S)).mono_fun'
    · exact (hgm.comp (measurable_id.prodMk
        (GaussianLocal.measurable_flight.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using hg (t,JetBarrier.flight t p))
  have H := TransportPrimitive.localized_damped hT hgi (hχ p) (hχ' p) (hdχ p)
    (L := L) (c := f₀ p)
  have hboundary := hpend.trans (value_along_flight ⟨hT,le_rfl⟩ L f₀ g p)
  rw [hboundary,H]
  congr 1
  rw [intervalIntegral.integral_of_le hT,intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  have he := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hpe
  filter_upwards [he] with t ht
  rw [ht]
  congr 1
  ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalCharacteristic
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Physical collision source in the localized characteristic equation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.PhysicalLocalization

theorem source_eq {q b L : ℝ} (F : ℝ × JetPrototype.Phase → ℝ)
    {p : JetPrototype.Phase} (hp : p.2 ∈ HotRepresentative.good q) (t : ℝ) :
    H q p.2*(forcing q b L F (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p)) =
      source b q F (t,JetBarrier.flight t p) := by
  exact HotRepresentative.physical_source_eq (q := q) (b := b) (L := L) (GaussianLocal.state F)
    (p := ((t,(JetBarrier.flight t p).1),(JetBarrier.flight t p).2)) hp

/-- The constructed positive periodic solutions satisfy the physical localized
Duhamel formula; the artificial iteration damping has disappeared. -/
theorem localized (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    (χ χ' : JetPrototype.Phase → ℝ → ℝ)
    (hχ : ∀ p, ContinuousOn (χ p) (Icc 0 T))
    (hχ' : ∀ p, ContinuousOn (χ' p) (Icc 0 T))
    (hdχ : ∀ p t, t ∈ Icc 0 T → HasDerivAt (χ p) (χ' p t) t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      χ p T*density q F.value (T,JetBarrier.flight T p) =
        Real.exp (-T)*χ p 0*(H q p.2*f₀ p) +
        ∫ t in 0..T, Real.exp (-(T-t)) *
          (χ p t*source b q F.value (t,JetBarrier.flight t p) +
            (χ' p t+χ p t)*density q F.value (t,JetBarrier.flight t p)) := by
  have hbound (z) : |forcing q b L F.value z| ≤ HotApplication.realBound q*R^2+L*R := by
    have h := HotRepresentative.source_bounds hq₂ hb hR hloss
      (GaussianLocal.measurable_state F.measurable_value)
      (fun p => F.value_bounds (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2)
    change 0 ≤ forcing q b L F.value z ∧ forcing q b L F.value z ≤ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hmild : ∀ t ∈ Icc 0 T, (fun p => F.value (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀
        (forcing q b L F.value) (t,p)) := by
    intro t ht
    refine (F.mild t ⟨ht.1,ht.2.trans hTU⟩).trans (ae_of_all _ (fun p => ?_))
    exact PositiveIntegral.value_eq_at_time ⟨ht.1,ht.2.trans hTU⟩ ht.2 L f₀
      (fun _ _ _ => rfl) p
  have hloc := PositiveIntegral.localized_characteristic hT hf₀ F.measurable_value
    (measurable_forcing F.measurable_value q b L) hbound hmild χ χ' hχ hχ' hdχ
  have hgood : ∀ᵐ p ∂FlightMeasure.phaseVolume, p.2 ∈ HotRepresentative.good q := by
    apply (Measure.ae_prod_iff_ae_ae ((HotRepresentative.measurableSet_good q).preimage measurable_snd)).mpr
    exact ae_of_all _ (fun _ => HotRepresentative.ae_good_q80 hcarleman hq₁ hq₂)
  filter_upwards [hloc,hgood] with p hp hpg
  have hmuleq := congrArg (fun r : ℝ => H q p.2*r) hp
  rw [mul_add,← intervalIntegral.integral_const_mul] at hmuleq
  calc
    _ = H q p.2*(χ p T*F.value (T,JetBarrier.flight T p)) := by
      dsimp [density,JetBarrier.flight]
      ring
    _ = _ := hmuleq
    _ = _ := by
      congr 1
      · ring
      · apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        have hsrc := source_eq (b := b) (L := L) F.value hpg t
        rw [← hsrc]
        dsimp [density,JetBarrier.flight]
        ring

end BoltzmannNonuniqueness.PhysicalLocalization

end

end

section

/-! # The undamped characteristic equation of the actual physical density -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.PhysicalLocalization

theorem characteristic (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      density q F.value (T,JetBarrier.flight T p) = H q p.2*f₀ p +
        ∫ t in 0..T, source b q F.value (t,JetBarrier.flight t p) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
    convert (hasDerivAt_neg t).exp using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have he := localized hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀
    (fun _ t => Real.exp (-t)) (fun _ t => -Real.exp (-t))
    (fun _ => (Real.continuous_exp.comp continuous_neg).continuousOn)
    (fun _ => (Real.continuous_exp.comp continuous_neg).neg.continuousOn)
    (fun _ t _ => hd t)
  filter_upwards [he] with p hp
  have hi : (∫ t in 0..T, Real.exp (-(T-t)) *
      (Real.exp (-t)*source b q F.value (t,JetBarrier.flight t p) +
        (-Real.exp (-t)+Real.exp (-t))*density q F.value (t,JetBarrier.flight t p))) =
      Real.exp (-T)*(∫ t in 0..T, source b q F.value (t,JetBarrier.flight t p)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [neg_add_cancel,zero_mul,add_zero,← mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [hi] at hp
  simp only [neg_zero,Real.exp_zero,mul_one] at hp
  apply (mul_left_cancel₀ (Real.exp_ne_zero (-T)))
  calc
    _ = Real.exp (-T)*(H q p.2*f₀ p) +
        Real.exp (-T)*(∫ t in 0..T, source b q F.value (t,JetBarrier.flight t p)) := by
      simpa only [mul_assoc] using hp
    _ = _ := (mul_add _ _ _).symm

end BoltzmannNonuniqueness.PhysicalLocalization

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_EuclideanKineticMap
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Euclidean coordinates for the physical characteristic equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem density_measurable {F : ℝ × JetPrototype.Phase → ℝ} (hF : Measurable F) (q : ℝ) :
    Measurable (density q F) := by
  have hphase : Measurable (fun z : Published.KineticPhase => phaseEquiv (z.1.2,z.2)) :=
    phaseEquiv.measurable.comp (measurable_fst.snd.prodMk measurable_snd)
  exact ((ChartKernel.measurable_H q).comp measurable_snd).mul
    (hF.comp (measurable_fst.fst.prodMk hphase))

theorem source_eq_collision (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    source b q F = CollisionCompactness.collisionSource b (density q F) := by
  funext z
  rfl

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Inverse free flight and Lebesgue preservation in Euclidean coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem characteristic_back (p : Velocity × Velocity) (t s : ℝ) :
    TransportCutoff.characteristic (flight (-t) p) s =
      ((s,p.1-(t-s) • p.2),p.2) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · dsimp [TransportCutoff.characteristic,flight]
      module
  · rfl

@[simp] theorem characteristic_endpoint (p : Velocity × Velocity) (t : ℝ) :
    TransportCutoff.characteristic (flight (-t) p) t = ((t,p.1),p.2) := by
  rw [characteristic_back]
  simp only [sub_self,zero_smul,sub_zero]

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Localized physical mild equation in the Euclidean GLPS coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem density_along (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (p : Velocity × Velocity) (t : ℝ) :
    density q F ((t,(flight t p).1),(flight t p).2) =
      PhysicalLocalization.density q F (t,JetBarrier.flight t (phaseEquiv p)) := by
  change PhysicalLocalization.density q F (t,phaseEquiv (flight t p)) = _
  rw [phaseEquiv_flight]

theorem source_along (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (p : Velocity × Velocity) (t : ℝ) :
    source b q F ((t,(flight t p).1),(flight t p).2) =
      PhysicalLocalization.source b q F (t,JetBarrier.flight t (phaseEquiv p)) := by
  change PhysicalLocalization.source b q F (t,phaseEquiv (flight t p)) = _
  rw [phaseEquiv_flight]

theorem localized (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    (χ χ' : (Velocity × Velocity) → ℝ → ℝ)
    (hχ : ∀ p, ContinuousOn (χ p) (Icc 0 T))
    (hχ' : ∀ p, ContinuousOn (χ' p) (Icc 0 T))
    (hdχ : ∀ p t, t ∈ Icc 0 T → HasDerivAt (χ p) (χ' p t) t) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ p T*density q F.value ((T,(flight T p).1),(flight T p).2) =
        Real.exp (-T)*χ p 0*(H q p.2*f₀ (phaseEquiv p)) +
        ∫ t in 0..T, Real.exp (-(T-t)) *
          (χ p t*source b q F.value ((t,(flight t p).1),(flight t p).2) +
            (χ' p t+χ p t)*density q F.value ((t,(flight t p).1),(flight t p).2)) := by
  have h := PhysicalLocalization.localized hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀
    (fun p => χ (phaseEquiv.symm p)) (fun p => χ' (phaseEquiv.symm p))
    (fun p => hχ _) (fun p => hχ' _) (fun p => hdχ _)
  have hp := phaseEquiv_measurePreserving.quasiMeasurePreserving.ae h
  filter_upwards [hp] with p hpp
  simp only [phaseEquiv.symm_apply_apply,phaseEquiv_snd] at hpp
  simpa only [density_along,source_along] using hpp

/-- A smooth kinetic cutoff, with its derivative actually computed along the
transport field, gives the local source required by velocity averaging. -/
theorem smooth_localized (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ (TransportCutoff.characteristic p T)*density q F.value (TransportCutoff.characteristic p T) =
        ∫ t in 0..T, Real.exp (-(T-t)) *
          (χ (TransportCutoff.characteristic p t)*source b q F.value (TransportCutoff.characteristic p t) +
            (TransportCutoff.transportDerivative χ (TransportCutoff.characteristic p t)+
              χ (TransportCutoff.characteristic p t))*density q F.value (TransportCutoff.characteristic p t)) := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have H := localized hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀
    (fun p t => χ (TransportCutoff.characteristic p t))
    (fun p t => TransportCutoff.transportDerivative χ (TransportCutoff.characteristic p t))
    (fun p => (hχ.continuous.comp (TransportCutoff.characteristic_continuous p)).continuousOn)
    (fun p => ((TransportCutoff.transportDerivative_continuous hχ).comp
      (TransportCutoff.characteristic_continuous p)).continuousOn)
    (fun p t _ => TransportCutoff.hasDerivAt_along hd p t)
  filter_upwards [H] with p hp
  rw [hzero p] at hp
  simpa only [mul_zero,zero_mul,zero_add,TransportCutoff.characteristic,flight] using hp

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # The physical integral equation in ordinary Euclidean coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem characteristic (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀) :
    ∀ᵐ p : Velocity × Velocity ∂volume,
      density q F.value ((T,p.1+T • p.2),p.2) = H q p.2*f₀ (phaseEquiv p) +
        ∫ t in 0..T, source b q F.value ((t,p.1+t • p.2),p.2) := by
  have h := phaseEquiv_measurePreserving.quasiMeasurePreserving.ae
    (PhysicalLocalization.characteristic hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀)
  filter_upwards [h] with p hp
  have he (t : ℝ) : phaseEquiv (p.1+t • p.2,p.2) = JetBarrier.flight t (phaseEquiv p) :=
    phaseEquiv_flight t p
  have hv : (phaseEquiv p).2 = p.2 := rfl
  simpa only [density,source,he,hv] using hp

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CappedDensitySequence
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Spacetime velocity moments of the actual capped periodic solutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem torusPhysical_measurable {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (q : ℝ) :
    Measurable (torusPhysical q F) := by
  have hrep : Measurable (fun z : (ℝ × Position) × Velocity => TorusChart.representative z.1.2) :=
    TorusChart.representative_measurePreserving.measurable.comp measurable_fst.snd
  have hspace := JetPeriodicDatum.spatialMap_measurePreserving.measurable.comp hrep
  have harg : Measurable (fun z : (ℝ × Position) × Velocity =>
      (z.1.1,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1.2),z.2))) :=
    measurable_fst.fst.prodMk (hspace.prodMk measurable_snd)
  have hw : Measurable (fun z : (ℝ × Position) × Velocity => H q z.2) := by
    unfold H singularity
    fun_prop
  exact hw.mul (hFm.comp harg)

theorem torusPhysical_nonneg {F : ℝ × JetPrototype.Phase → ℝ} (hF : ∀ u, 0 ≤ F u)
    (q : ℝ) (z : (ℝ × Position) × Velocity) : 0 ≤ torusPhysical q F z :=
  mul_nonneg (H_nonneg q z.2) (hF _)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CausalConvolution
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The causal resolvent is a finite characteristic integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

theorem causal_convolution {r : ℝ → ℝ} (hr : ∀ s < 0, r s = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Ici (0:ℝ), Real.exp (-s)*r (t-s)) =
      ∫ s in 0..t, Real.exp (-(t-s))*r s := by
  have he : (∫ s in Ici (0:ℝ), Real.exp (-s)*r (t-s)) =
      ∫ s in Ici (0:ℝ), (Icc 0 t).indicator (fun s => Real.exp (-s)*r (t-s)) s := by
    apply setIntegral_congr_fun measurableSet_Ici
    intro s hs
    by_cases hst : s ≤ t
    · rw [indicator_of_mem (show s ∈ Icc 0 t from ⟨hs,hst⟩)]
    · rw [indicator_of_notMem (show s ∉ Icc 0 t from fun h => hst h.2)]
      change Real.exp (-s)*r (t-s) = 0
      rw [hr (t-s) (by linarith),mul_zero]
  rw [he,integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hset : Icc 0 t ∩ Ici 0 = Icc (0:ℝ) t := inter_eq_left.mpr (fun _ h => h.1)
  rw [hset,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht]
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun s => Real.exp (-(t-s))*r s) t (a := 0) (b := t)
  simp only [sub_self,sub_zero] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [sub_sub_cancel]

/-- Finite-time formula for exactly the Euclidean resolvent appearing in the
published GLPS hypothesis. No time differentiability is used here. -/
theorem transportResolvent_eq {r : Published.KineticPhase → ℝ}
    (hr : ∀ z, z.1.1 < 0 → r z = 0) (z : Published.KineticPhase) (ht : 0 ≤ z.1.1) :
    Published.transportResolvent r z =
      ∫ t in 0..z.1.1, Real.exp (-(z.1.1-t))*r ((t,z.1.2-(z.1.1-t) • z.2),z.2) := by
  have H := causal_convolution
    (r := fun t => r ((t,z.1.2-(z.1.1-t) • z.2),z.2))
    (fun s hs => hr _ hs) ht
  have he : Published.transportResolvent r z =
      ∫ s in Ici (0:ℝ), Real.exp (-s)*r ((z.1.1-s,z.1.2-(z.1.1-(z.1.1-s)) • z.2),z.2) := by
    unfold Published.transportResolvent
    simp only [sub_sub_cancel]
  exact he.trans H

end BoltzmannNonuniqueness.TransportPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AveragingTailSources
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A GLPS diagonal for countably many localized sources and velocity tests

The resolvent compactness hypothesis yields a common diagonal subsequence
for the countable family.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

theorem GLPS1988Proposition3.countable_sources_tests (hGLPS : GLPS1988Proposition3)
    (r : ℕ → ℕ → KineticPhase → ℝ) (R : ℕ → ℝ) (hR : ∀ j, 0 < R j)
    (hsupp : ∀ j n, ∀ᵐ z ∂(volume : Measure KineticPhase), R j < ‖z.2‖ → r j n z = 0)
    (hUI : ∀ j, UniformIntegrable (r j) 1 volume)
    (ψ : ℕ → Velocity → ℝ)
    (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocalL1Converges (fun n => resolventAverage (r j (φ n)) (ψ j)) (g j) := by
  have hsub (j : ℕ) (a : ℕ → ℕ) : UniformIntegrable (fun n => r j (a n)) 1 volume := by
    obtain ⟨hu,C,hC⟩ := hUI j
    exact ⟨hu.comp a,C,fun n => hC (a n)⟩
  have hex (j : ℕ) (a : ℕ → ℕ) := hGLPS (fun n => r j (a n)) (R j) (hR j)
    (fun n => hsupp j (a n)) (hsub j a) (ψ j) (hψ j) (hψc j)
  choose σ g hσ hg using hex
  let a : ℕ → ℕ → ℕ := fun n => Nat.rec id (fun j aj => aj ∘ σ j aj) n
  have has (j : ℕ) : a (j+1) = a j ∘ σ j (a j) := rfl
  have ha (j : ℕ) : StrictMono (a j) := by
    induction j with
    | zero => exact strictMono_id
    | succ j hj => rw [has]; exact hj.comp (hσ j (a j))
  have hnest (i j : ℕ) (hij : i ≤ j) :
      ∀ k, ∃ m, k ≤ m ∧ a i m = a j k := by
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      exact fun k => ⟨k,le_rfl,rfl⟩
    | succ j ih =>
      by_cases hi : i ≤ j
      · intro k
        obtain ⟨m,hm,he⟩ := ih hi (σ j (a j) k)
        exact ⟨m,((hσ j (a j)).id_le k).trans hm,he⟩
      · have he : i = j+1 := by omega
        subst i
        exact fun k => ⟨k,le_rfl,rfl⟩
  let φ : ℕ → ℕ := fun n => a (n+1) n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change a (n+1) n < a (n+2) (n+1)
    rw [has (n+1)]
    exact (ha (n+1)) ((Nat.lt_succ_self n).trans_le ((hσ (n+1) (a (n+1))).id_le (n+1)))
  refine ⟨φ,fun j => g j (a j),hφ,?_⟩
  intro j
  have hj : LocalL1Converges (fun n => resolventAverage (r j (a (j+1) n)) (ψ j)) (g j (a j)) :=
    hg j (a j)
  let ρ : ℕ → ℕ := fun n => if hn : j+1 ≤ n+1 then (hnest (j+1) (n+1) hn n).choose else n
  have hρ (n : ℕ) : n ≤ ρ n := by
    dsimp only [ρ]
    split_ifs with hn
    · exact (hnest (j+1) (n+1) hn n).choose_spec.1
    · exact le_rfl
  have hρtop : Tendsto ρ atTop atTop := tendsto_atTop_mono hρ tendsto_id
  have he : ∀ᶠ n in atTop, a (j+1) (ρ n) = φ n := by
    filter_upwards [eventually_ge_atTop j] with n hn
    have hn' : j+1 ≤ n+1 := by omega
    exact (by
      dsimp only [ρ]
      rw [dite_eq_left hn']
      exact (hnest (j+1) (n+1) hn' n).choose_spec.2)
  refine ⟨hj.1,fun K hK => ?_⟩
  apply ((hj.2 K hK).comp hρtop).congr'
  filter_upwards [he] with n hn
  simp only [Function.comp_apply]
  rw [hn]

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_MeasurableResolvent
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurability of the exact transport resolvent and its velocity averages -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Published

theorem transportResolvent_measurable {r : KineticPhase → ℝ} (hr : Measurable r) :
    Measurable (transportResolvent r) := by
  have hm : Measurable (fun p : KineticPhase × ℝ =>
      Real.exp (-p.2)*r ((p.1.1.1-p.2,p.1.1.2-p.2 • p.1.2),p.1.2)) := by
    exact (by fun_prop : Measurable (fun p : KineticPhase × ℝ => Real.exp (-p.2))).mul
      (hr.comp (by fun_prop))
  exact hm.stronglyMeasurable.integral_prod_right.measurable

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TimeSourceCumulative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
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

theorem timePrimitive_integrable {μ : Measure ℝ} {ν : Measure P}
    [IsFiniteMeasure μ] [SFinite ν] {f : ℝ × P → ℝ}
    (hfm : Measurable f) (hfi : Integrable f (μ.prod ν)) :
    Integrable (timePrimitive μ f) (μ.prod ν) := by
  have h : WeakL1Converges (μ.prod ν) (fun _ : ℕ => f) f :=
    ⟨hfm,hfi,fun _ _ _ => tendsto_const_nhds⟩
  exact (h.timePrimitive (fun _ => hfm) (fun _ => hfi)).2.1

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Restricting local L¹ convergence to the physical time interval -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

theorem LocalL1Converges.time_restrict {T : ℝ} {f a : ℕ → SpaceTime → ℝ} {g : SpaceTime → ℝ}
    (h : LocalL1Converges f g) (he : ∀ n, a n =ᵐ[timeSpaceVolume T] f n) :
    TimeLocalL1Converges T a g := by
  refine ⟨h.1,fun K hK => ?_⟩
  have hμ : timeSpaceVolume T ≤ (volume : Measure SpaceTime) :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hn (n) : eLpNorm (fun z => a n z-g z) 1 ((timeSpaceVolume T).restrict K) =
      eLpNorm (fun z => f n z-g z) 1 ((timeSpaceVolume T).restrict K) := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_of_ae (he n)] with z hz
    rw [hz]
  simp_rw [hn]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h.2 K hK)
    (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ (Measure.restrict_mono_measure hμ K))

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_ResolventAverageBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual local solutions are the precise published transport resolvents -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem resolvent_representation (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ ((T,p.1),p.2)*density q F.value ((T,p.1),p.2) =
        Published.transportResolvent
          (localizedSource U χ (density q F.value) (source b q F.value)) ((T,p.1),p.2) := by
  have hl := smooth_localized hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀ hχ hzero
  have hback := (flight_measurePreserving (-T)).quasiMeasurePreserving.ae hl
  filter_upwards [hback] with p hp
  simp only [characteristic_endpoint,characteristic_back] at hp
  rw [TransportPrimitive.transportResolvent_eq
    (fun z hz => localizedSource_causal U χ _ _ z hz) _ hT]
  rw [hp]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  dsimp only
  rw [localizedSource_on χ _ _ _ ⟨ht.1,ht.2.trans hTU⟩]

end BoltzmannNonuniqueness.EuclideanFlight

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

/-! # Resolvent representation on spacetime, including actual velocity averages -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem spacetime_resolvent (hcarleman : Published.GPV2009CarlemanInput)
    {q b L U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    (fun z => χ z*density q F.value z) =ᵐ[
      ((volume.restrict (Icc 0 U)).prod (volume : Measure Velocity)).prod volume]
      Published.transportResolvent (localizedSource U χ (density q F.value) (source b q F.value)) := by
  let f := density q F.value
  let r := localizedSource U χ f (source b q F.value)
  have hfm : Measurable f := density_measurable F.measurable_value q
  have hQm : Measurable (source b q F.value) := by
    rw [source_eq_collision]
    exact CollisionCompactness.collisionSource_measurable hfm b
  have hrm : Measurable r := localizedSource_measurable hχ hfm hQm
  have hm : MeasurableSet {z : ℝ × (Velocity × Velocity) |
      χ ((z.1,z.2.1),z.2.2)*f ((z.1,z.2.1),z.2.2) =
        Published.transportResolvent r ((z.1,z.2.1),z.2.2)} := by
    exact (measurableSet_eq_fun (hχ.continuous.measurable.mul hfm)
      (Published.transportResolvent_measurable hrm)).preimage (by fun_prop)
  have ht : ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ ((t,p.1),p.2)*f ((t,p.1),p.2) = Published.transportResolvent r ((t,p.1),p.2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact resolvent_representation hcarleman F hq₁ hq₂ hb hR ht.1 ht.2 hloss hf₀ hχ hzero
  have hfull := (Measure.ae_prod_iff_ae_ae hm).mpr ht
  exact (measurePreserving_prodAssoc (volume.restrict (Icc 0 U))
    (volume : Measure Velocity) (volume : Measure Velocity)).quasiMeasurePreserving.ae hfull

theorem velocity_averages_resolvent (hcarleman : Published.GPV2009CarlemanInput)
    {q b L U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0)
    (ψ : Velocity → ℝ) :
    (fun z : Published.SpaceTime => ∫ v, ψ v*(χ (z,v)*density q F.value (z,v))) =ᵐ[
      (volume.restrict (Icc 0 U)).prod (volume : Measure Velocity)]
      Published.resolventAverage (localizedSource U χ (density q F.value) (source b q F.value)) ψ := by
  have he := Measure.ae_ae_of_ae_prod
    (spacetime_resolvent hcarleman F hq₁ hq₂ hb hR hloss hf₀ hχ hzero)
  filter_upwards [he] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with v hv
  rw [hv]

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AveragedPairIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform integrability of products of bounded velocity averages -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem uniformIntegrable_average_product
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [IsFiniteMeasure ν]
    {f : ℕ → X × Y → ℝ} (hf : ∀ n, Measurable (f n))
    (hui : UniformIntegrable (fun (n : ℕ) (z : X × (Y × Y)) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) 1 (μ.prod (ν.prod ν)))
    {k l : X × Y → ℝ} (hk : Measurable k) (hl : Measurable l)
    (C D : ℝ≥0) (hC : ∀ z, |k z| ≤ C) (hD : ∀ z, |l z| ≤ D) :
    UniformIntegrable (fun n x => (∫ v, k (x,v)*f n (x,v) ∂ν)*
      (∫ w, l (x,w)*f n (x,w) ∂ν)) 1 μ := by
  let a : X × (Y × Y) → ℝ := fun z => k (z.1,z.2.1)*l (z.1,z.2.2)
  have ha : Measurable a := by dsimp [a]; fun_prop
  have haB : ∀ z, |a z| ≤ (C*D : ℝ≥0) := by
    intro z
    dsimp [a]
    rw [abs_mul]
    exact mul_le_mul (hC _) (hD _) (abs_nonneg _) C.coe_nonneg
  have hmul := uniformIntegrable_of_bounded_multiplier hui ha (C*D) haB
  have hm (n) : Measurable (fun z : X × (Y × Y) =>
      a z*(f n (z.1,z.2.1)*f n (z.1,z.2.2))) := by fun_prop
  have hint := uniformIntegrable_integral hm hmul
  have he (n) (x) : (∫ y : Y × Y, a (x,y)*(f n (x,y.1)*f n (x,y.2)) ∂ν.prod ν) =
      (∫ v, k (x,v)*f n (x,v) ∂ν)*(∫ w, l (x,w)*f n (x,w) ∂ν) := by
    rw [← integral_prod_mul]
    congr 1
    ext y
    dsimp [a]
    ring
  simpa only [he] using hint

/-- Compact velocity support reduces the infinite velocity measure to finite fibres. -/
theorem uniformIntegrable_average_product_of_support
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {s : Set Y} [IsFiniteMeasure (ν.restrict s)]
    {f : ℕ → X × Y → ℝ} (hf : ∀ n, Measurable (f n))
    (hui : UniformIntegrable (fun (n : ℕ) (z : X × (Y × Y)) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) 1 (μ.prod (ν.prod ν)))
    {k l : X × Y → ℝ} (hk : Measurable k) (hl : Measurable l)
    (C D : ℝ≥0) (hC : ∀ z, |k z| ≤ C) (hD : ∀ z, |l z| ≤ D)
    (hks : ∀ x y, y ∉ s → k (x,y) = 0) (hls : ∀ x y, y ∉ s → l (x,y) = 0) :
    UniformIntegrable (fun n x => (∫ v, k (x,v)*f n (x,v) ∂ν)*
      (∫ w, l (x,w)*f n (x,w) ∂ν)) 1 μ := by
  have hp := uniformIntegrable_restrict hui (univ ×ˢ (s ×ˢ s))
  rw [← Measure.prod_restrict,Measure.restrict_univ,← Measure.prod_restrict] at hp
  have h := uniformIntegrable_average_product hf hp hk hl C D hC hD
  have he (n) (x) : (∫ v in s, k (x,v)*f n (x,v) ∂ν) = ∫ v, k (x,v)*f n (x,v) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hks x y hy,zero_mul])
  have he' (n) (x) : (∫ v in s, l (x,v)*f n (x,v) ∂ν) = ∫ v, l (x,v)*f n (x,v) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hls x y hy,zero_mul])
  simpa only [he,he'] using h

end BoltzmannNonuniqueness.Compactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CompactCapFamily
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong local product convergence from pair uniform integrability -/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

open Published

theorem uniformIntegrable_compact_average_product {μ : Measure SpaceTime} [SFinite μ]
    {f : ℕ → KineticPhase → ℝ} (hf : ∀ n, Measurable (f n))
    (hui : UniformIntegrable (fun (n : ℕ) (z : SpaceTime × (Velocity × Velocity)) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) 1 (μ.prod volume))
    {k l : KineticPhase → ℝ} (hk : Continuous k) (hl : Continuous l)
    (hkc : HasCompactSupport k) (hlc : HasCompactSupport l) :
    UniformIntegrable (fun n x => (∫ v, k (x,v)*f n (x,v))*
      (∫ w, l (x,w)*f n (x,w))) 1 μ := by
  obtain ⟨R,_hR,hball⟩ := ((hkc.union hlc).image continuous_snd).isBounded.subset_ball_lt
    0 (0 : Velocity)
  have hs (z : KineticPhase) (hz : z.2 ∉ Metric.closedBall (0 : Velocity) R) :
      k z = 0 ∧ l z = 0 := by
    have hn : z ∉ tsupport k ∪ tsupport l := by
      intro h
      have hb := hball (mem_image_of_mem Prod.snd h)
      exact hz (Metric.ball_subset_closedBall hb)
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inl h)),
      image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inr h))⟩
  obtain ⟨C,hC⟩ := hk.bounded_above_of_compact_support hkc
  obtain ⟨D,hD⟩ := hl.bounded_above_of_compact_support hlc
  let : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  apply uniformIntegrable_average_product_of_support (s := Metric.closedBall (0 : Velocity) R)
    hf (by simpa only [Measure.volume_eq_prod] using hui) hk.measurable hl.measurable
    (⟨max C 0,le_max_right _ _⟩ : ℝ≥0) (⟨max D 0,le_max_right _ _⟩ : ℝ≥0)
    (fun z => (hC z).trans (le_max_left _ _))
    (fun z => (hD z).trans (le_max_left _ _))
  · exact fun x v hv => (hs (x,v) hv).1
  · exact fun x v hv => (hs (x,v) hv).2

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The constructed cap sequence and its compactness bounds

The actual positive cutoff solutions satisfy bounds sufficient for the
compactness and limit constructions.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.source_ui {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.collisionSource (N+1)
      (torusPhysical q (F.approximation N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume F.time).prod (volume : Measure Velocity)) :=
  CollisionCompactness.collisionSource_uniformIntegrable
    (fun N => torusPhysical_measurable (F.approximation N).solution.measurable_value q)
    (fun N => torusPhysical_nonneg (fun z => ((F.approximation N).solution.value_bounds z).1) q)
    F.pairs_ui (fun N => N+1) F.gain_ui F.loss_ui

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusCharacteristic
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Transfer of the actual cap sequence to the Euclidean fundamental cell -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.TorusKineticChart

theorem measurePreserving (T : ℝ) : MeasurePreserving chart
    ((AnnularEnvelope.timePositionVolume T).prod volume) (cellVolume T) :=
  ((MeasurePreserving.id (volume.restrict (Icc 0 T))).prod
    TorusChart.representative_measurePreserving).prod (MeasurePreserving.id volume)

theorem density_comp (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    EuclideanFlight.density q F ∘ chart = JetCopyDatum.torusPhysical q F := by
  funext z
  simp only [Function.comp_apply,EuclideanFlight.density,chart,
    EuclideanFlight.phaseEquiv_apply,PhysicalLocalization.density,
    JetPeriodicDatum.phaseMap,JetCopyDatum.torusPhysical]

theorem source_comp (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    EuclideanFlight.source b q F ∘ chart =
      CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F) := by
  rw [EuclideanFlight.source_eq_collision]
  funext z
  have hd (v : Velocity) : EuclideanFlight.density q F (chart (z.1,v)) =
      JetCopyDatum.torusPhysical q F (z.1,v) := congrFun (density_comp q F) (z.1,v)
  simp only [Function.comp_apply,CollisionCompactness.collisionSource,
    KineticCollisionNullSets.gain,KineticCollisionNullSets.frequency]
  simp only [chart] at hd ⊢
  simp_rw [hd]

end BoltzmannNonuniqueness.TorusKineticChart

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.density_ui_cell {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun n => EuclideanFlight.density q (F.approximation n).solution.value) 1
      (TorusKineticChart.cellVolume F.time) := by
  apply Compactness.uniformIntegrable_of_comp_measurePreserving
    (TorusKineticChart.measurePreserving F.time)
    (fun n => EuclideanFlight.density_measurable (F.approximation n).solution.measurable_value q)
  simpa only [TorusKineticChart.density_comp] using F.density_ui

theorem CompactCapFamily.source_ui_cell {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun n : ℕ => EuclideanFlight.source (n+1) q (F.approximation n).solution.value) 1
      (TorusKineticChart.cellVolume F.time) := by
  have hm (n : ℕ) : Measurable (EuclideanFlight.source (n+1) q (F.approximation n).solution.value) := by
    rw [EuclideanFlight.source_eq_collision]
    exact CollisionCompactness.collisionSource_measurable
      (EuclideanFlight.density_measurable (F.approximation n).solution.measurable_value q) (n+1)
  apply Compactness.uniformIntegrable_of_comp_measurePreserving
    (TorusKineticChart.measurePreserving F.time) hm
  simpa only [TorusKineticChart.source_comp] using F.source_ui

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The periodic Euclidean density descends to the actual spatial torus -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusPeriodicity

private theorem exists_lattice_difference {x y : Velocity}
    (h : torusProjection x = torusProjection y) :
    ∃ n : JetLattice.Lattice, ∀ i, x i-y i = (n i : ℝ) := by
  have hc i : ((x i-y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr (congrFun h i)
  have hn i : ∃ n : ℤ, x i-y i = (n : ℝ) := by
    obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hc i)
    refine ⟨n,?_⟩
    have hn' : (n : ℝ) = x i-y i := by simpa only [zsmul_eq_mul,mul_one] using hn
    exact hn'.symm
  choose n hn using hn
  exact ⟨n,hn⟩

private theorem spatial_difference {x y : Velocity} {n : JetLattice.Lattice}
    (hn : ∀ i, x i-y i = (n i : ℝ)) :
    JetPeriodicDatum.spatialMap x-JetCopyDatum.displacement n = JetPeriodicDatum.spatialMap y := by
  apply Prod.ext
  · ext i
    change x i.castSucc-(n i.castSucc : ℝ) = y i.castSucc
    linarith [hn i.castSucc]
  · change x (Fin.last 2)-(n (Fin.last 2) : ℝ) = y (Fin.last 2)
    linarith [hn (Fin.last 2)]

theorem density_eq_of_projection_eq {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, WeightedTranslation.pull (JetCopyDatum.displacement n) F = F)
    {x y : Velocity} (h : torusProjection x = torusProjection y) (q t : ℝ) (v : Velocity) :
    EuclideanFlight.density q F ((t,x),v) = EuclideanFlight.density q F ((t,y),v) := by
  obtain ⟨n,hn⟩ := exists_lattice_difference h
  have he := congrFun (hF n) (t,(JetPeriodicDatum.spatialMap x,v))
  change F (t,(JetPeriodicDatum.spatialMap x-JetCopyDatum.displacement n,v)) =
    F (t,(JetPeriodicDatum.spatialMap x,v)) at he
  rw [spatial_difference hn] at he
  simp only [EuclideanFlight.density,PhysicalLocalization.density,EuclideanFlight.phaseEquiv_apply,
    JetPeriodicDatum.phaseMap]
  rw [he]

theorem density_descends {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, WeightedTranslation.pull (JetCopyDatum.displacement n) F = F)
    (q t : ℝ) (x v : Velocity) :
    JetCopyDatum.torusPhysical q F ((t,torusProjection x),v) =
      EuclideanFlight.density q F ((t,x),v) := by
  have he := density_eq_of_projection_eq hF (TorusChart.projection_representative (torusProjection x)) q t v
  simpa only [JetCopyDatum.torusPhysical,EuclideanFlight.density,PhysicalLocalization.density,
    EuclideanFlight.phaseEquiv_apply,JetPeriodicDatum.phaseMap] using he

theorem source_descends {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, WeightedTranslation.pull (JetCopyDatum.displacement n) F = F)
    (b q t : ℝ) (x v : Velocity) :
    CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F) ((t,torusProjection x),v) =
      EuclideanFlight.source b q F ((t,x),v) := by
  rw [EuclideanFlight.source_eq_collision]
  simp only [CollisionCompactness.collisionSource,KineticCollisionNullSets.gain,
    KineticCollisionNullSets.frequency]
  simp_rw [density_descends hF]

end BoltzmannNonuniqueness.TorusPeriodicity

end

end

section

/-! # Actual pair-product compactness in the Euclidean fundamental cell -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusKineticChart

theorem pair_measurePreserving (T : ℝ) : MeasurePreserving pairChart
    ((AnnularEnvelope.timePositionVolume T).prod volume) (pairCellVolume T) :=
  ((MeasurePreserving.id (volume.restrict (Set.Icc 0 T))).prod
    TorusChart.representative_measurePreserving).prod (MeasurePreserving.id volume)

theorem pair_comp (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    CollisionCompactness.pairProduct (EuclideanFlight.density q F) ∘ pairChart =
      CollisionCompactness.pairProduct (JetCopyDatum.torusPhysical q F) := by
  funext z
  have h (v : Velocity) := congrFun (density_comp q F) (z.1,v)
  dsimp only [Function.comp_apply] at h
  change EuclideanFlight.density q F (chart (z.1,z.2.1))*
    EuclideanFlight.density q F (chart (z.1,z.2.2)) = _
  rw [h,h]
  rfl

end BoltzmannNonuniqueness.TorusKineticChart

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.raw_pairs_ui_cell {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun n => CollisionCompactness.pairProduct
      (EuclideanFlight.density q (F.approximation n).solution.value)) 1
      (TorusKineticChart.pairCellVolume F.time) := by
  have hm (n) := torusPhysical_measurable (F.approximation n).solution.measurable_value q
  have hn (n) (z) := torusPhysical_nonneg
    (fun u => ((F.approximation n).solution.value_bounds u).1) q z
  have hp := CollisionCompactness.pairProduct_uniformIntegrable hm hn F.pairs_ui
  apply Compactness.uniformIntegrable_of_comp_measurePreserving
    (TorusKineticChart.pair_measurePreserving F.time)
    (fun n => CollisionCompactness.pairProduct_measurable
      (EuclideanFlight.density_measurable (F.approximation n).solution.measurable_value q))
  simpa only [TorusKineticChart.pair_comp] using hp

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Euclidean representatives of the actual torus weak limits -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusKineticChart

theorem projection_measurable : Measurable torusProjection := by
  unfold torusProjection
  fun_prop

theorem liftDensity_measurable {g : (ℝ × Position) × Velocity → ℝ} (hg : Measurable g) :
    Measurable (liftDensity g) := by
  apply hg.comp
  exact (measurable_fst.fst.prodMk (projection_measurable.comp measurable_fst.snd)).prodMk measurable_snd

theorem liftPair_measurable {W : (ℝ × Position) × (Velocity × Velocity) → ℝ} (hW : Measurable W) :
    Measurable (liftPair W) := by
  apply hW.comp
  exact (measurable_fst.fst.prodMk (projection_measurable.comp measurable_fst.snd)).prodMk measurable_snd

theorem liftDensity_comp (g : (ℝ × Position) × Velocity → ℝ) : liftDensity g ∘ chart = g := by
  funext z
  simp only [Function.comp_apply,liftDensity,chart,TorusChart.projection_representative]

theorem liftPair_comp (W : (ℝ × Position) × (Velocity × Velocity) → ℝ) :
    liftPair W ∘ pairChart = W := by
  funext z
  simp only [Function.comp_apply,liftPair,pairChart,TorusChart.projection_representative]

theorem weak_density_transfer {T q : ℝ} {F : ℕ → ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, Measurable (F n)) {g : (ℝ × Position) × Velocity → ℝ}
    (h : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume T).prod volume)
      (fun n => JetCopyDatum.torusPhysical q (F n)) g) :
    Published.WeakL1Converges (cellVolume T) (fun n => EuclideanFlight.density q (F n))
      (liftDensity g) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (measurePreserving T)
    (fun n => EuclideanFlight.density_measurable (hF n) q) (liftDensity_measurable h.1)
  simpa only [density_comp,liftDensity_comp] using h

theorem weak_pair_transfer {T q : ℝ} {F : ℕ → ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, Measurable (F n)) {W : (ℝ × Position) × (Velocity × Velocity) → ℝ}
    (h : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume T).prod volume)
      (fun n => CollisionCompactness.pairProduct (JetCopyDatum.torusPhysical q (F n))) W) :
    Published.WeakL1Converges (pairCellVolume T)
      (fun n => CollisionCompactness.pairProduct (EuclideanFlight.density q (F n))) (liftPair W) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (pair_measurePreserving T)
    (fun n => CollisionCompactness.pairProduct_measurable
      (EuclideanFlight.density_measurable (hF n) q)) (liftPair_measurable h.1)
  simpa only [pair_comp,liftPair_comp] using h

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # The constructed approximations satisfy the characteristic equation on the torus -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.TorusFlight

theorem projection_flight (t : ℝ) (p : Phase) :
    (flight t p).1 = torusProjection (TorusChart.representative p.1+t • p.2) := by
  funext i
  have hp := congrFun (TorusChart.projection_representative p.1) i
  change p.1 i+(t*p.2 i : ℝ) = ((TorusChart.representative p.1 i+t*p.2 i : ℝ) : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add]
  exact congrArg (fun x : AddCircle (1 : ℝ) => x+(t*p.2 i : ℝ)) hp.symm

theorem characteristic (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀) :
    ∀ᵐ p : Phase ∂volume,
      JetCopyDatum.torusPhysical q F.value ((T,(flight T p).1),(flight T p).2) =
        initialDensity q f₀ p + ∫ t in 0..T,
          CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F.value)
            ((t,(flight t p).1),(flight t p).2) := by
  have hE := EuclideanFlight.characteristic hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀
  have h := TorusChart.phase_measurePreserving.quasiMeasurePreserving.ae (ae_restrict_of_ae hE)
  filter_upwards [h] with p hp
  have hd t : JetCopyDatum.torusPhysical q F.value ((t,(flight t p).1),(flight t p).2) =
      EuclideanFlight.density q F.value ((t,TorusChart.representative p.1+t • p.2),p.2) := by
    rw [projection_flight]
    exact TorusPeriodicity.density_descends F.periodic q t _ p.2
  have hs t : CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F.value)
      ((t,(flight t p).1),(flight t p).2) =
      EuclideanFlight.source b q F.value ((t,TorusChart.representative p.1+t • p.2),p.2) := by
    rw [projection_flight]
    exact TorusPeriodicity.source_descends F.periodic b q t _ p.2
  rw [hd]
  simp_rw [hs]
  simpa only [initialDensity,EuclideanFlight.phaseEquiv_apply,TorusChart.phaseRepresentative] using hp

end BoltzmannNonuniqueness.TorusFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CellLocalizedSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The finite spacetime measure of the fundamental cell -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusKineticChart

instance instIsFiniteMeasureSpaceTimeBaseVolume (T : ℝ) : IsFiniteMeasure (baseVolume T) := by
  have he := TorusChart.representative_measurePreserving.map_eq
  have : IsFiniteMeasure ((volume : Measure Velocity).restrict TorusChart.cube) := by
    rw [← he]
    exact Measure.isFiniteMeasure_map volume TorusChart.representative
  unfold baseVolume
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem baseVolume_le (T : ℝ) : baseVolume T ≤ Published.timeSpaceVolume T :=
  Measure.prod_mono le_rfl Measure.restrict_le_self

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # Uniform integrability of actual localized Euclidean transport sources -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.TorusKineticChart

theorem measurableSet_region (U : ℝ) : MeasurableSet (region U) :=
  (measurableSet_Icc.prod TorusChart.measurableSet_cube).prod MeasurableSet.univ

theorem cellVolume_eq (U : ℝ) : cellVolume U = (volume : Measure KineticPhase).restrict (region U) := by
  unfold cellVolume region
  calc
    _ = (((volume : Measure ℝ).prod (volume : Measure Velocity)).restrict
        (Icc 0 U ×ˢ TorusChart.cube)).prod ((volume : Measure Velocity).restrict univ) := by
      rw [Measure.restrict_univ,Measure.prod_restrict]
    _ = _ := Measure.prod_restrict _ _

theorem localizedSource_eq {U : ℝ} {χ : KineticPhase → ℝ}
    (hχ : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube}) (f Q : KineticPhase → ℝ) :
    localizedSource U χ f Q = fun z =>
      χ z*(region U).indicator Q z+(transportDerivative χ z+χ z)*(region U).indicator f z := by
  funext z
  by_cases ht : z.1.1 ∈ Icc 0 U
  · by_cases hx : z.1.2 ∈ TorusChart.cube
    · have hz : z ∈ region U := ⟨⟨ht,hx⟩,mem_univ _⟩
      simp only [localizedSource,ite_eq_left ht,indicator_of_mem hz]
    · have hn : z ∉ tsupport χ := fun h => hx (hχ h)
      have hc := image_eq_zero_of_notMem_tsupport hn
      have hd := transportDerivative_eq_zero hn
      simp only [localizedSource,ite_eq_left ht,hc,hd,zero_mul,zero_add]
  · have hz : z ∉ region U := fun h => ht h.1.1
    simp only [localizedSource,ite_eq_right ht,indicator_of_notMem hz,mul_zero,zero_add]

private theorem uniformIntegrable_add {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : ℕ → X → ℝ} (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (fun n x => f n x+g n x) 1 μ := by
  obtain ⟨hu,C,hC⟩ := hf
  obtain ⟨hv,D,hD⟩ := hg
  refine ⟨hu.add hv (by norm_num),C+D,fun n => ?_⟩
  exact (eLpNorm_add_le (hf := hu.aestronglyMeasurable n) (hg := hv.aestronglyMeasurable n) (by norm_num : (1:ℝ≥0∞) ≤ 1)).trans
    (by simpa only [ENNReal.coe_add] using add_le_add (hC n) (hD n))

theorem localizedSource_uniformIntegrable {U : ℝ} {χ : KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube})
    {f Q : ℕ → KineticPhase → ℝ}
    (hf : UniformIntegrable f 1 (cellVolume U)) (hQ : UniformIntegrable Q 1 (cellVolume U)) :
    UniformIntegrable (fun n => localizedSource U χ (f n) (Q n)) 1 volume := by
  have hf0 := Compactness.uniformIntegrable_indicator_of_restrict (measurableSet_region U)
    (cellVolume_eq U ▸ hf)
  have hQ0 := Compactness.uniformIntegrable_indicator_of_restrict (measurableSet_region U)
    (cellVolume_eq U ▸ hQ)
  obtain ⟨C,hC⟩ := hχ.continuous.bounded_above_of_compact_support hc
  let D : KineticPhase → ℝ := fun z => transportDerivative χ z+χ z
  have hDm : Continuous D := (transportDerivative_continuous hχ).add hχ.continuous
  have hDc : HasCompactSupport D := (transportDerivative_hasCompactSupport hc).add hc
  obtain ⟨B,hB⟩ := hDm.bounded_above_of_compact_support hDc
  have h1 := Compactness.uniformIntegrable_of_bounded_multiplier hQ0 hχ.continuous.measurable
    (⟨max C 0,le_max_right _ _⟩ : ℝ≥0)
    (fun z => (show |χ z| ≤ C from hC z).trans (le_max_left _ _))
  have h2 := Compactness.uniformIntegrable_of_bounded_multiplier hf0 hDm.measurable
    (⟨max B 0,le_max_right _ _⟩ : ℝ≥0)
    (fun z => (show |D z| ≤ B from hB z).trans (le_max_left _ _))
  have H := uniformIntegrable_add h1 h2
  simpa only [localizedSource_eq hs,D] using H

end BoltzmannNonuniqueness.TorusKineticChart

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.localized_source_ui {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) {χ : Published.KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube}) :
    UniformIntegrable (fun n : ℕ => TransportCutoff.localizedSource F.time χ
      (EuclideanFlight.density q (F.approximation n).solution.value)
      (EuclideanFlight.source (n+1) q (F.approximation n).solution.value)) 1 volume :=
  TorusKineticChart.localizedSource_uniformIntegrable hχ hc hs F.density_ui_cell F.source_ui_cell

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalL1ApproximationLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.TorusKineticChart.instIsFiniteMeasureSpaceTimeBaseVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local factorization of pair moments along the actual averaging subsequence -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

theorem local_pair_moment_factorization {T : ℝ} {μ : Measure SpaceTime} [SFinite μ]
    (hμ : μ ≤ timeSpaceVolume T)
    {f : ℕ → KineticPhase → ℝ} {g : KineticPhase → ℝ}
    {W : SpaceTime × (Velocity × Velocity) → ℝ}
    (hfm : ∀ n, Measurable (f n))
    (hfi : ∀ n, Integrable (f n) (μ.prod volume))
    (hpUI : UniformIntegrable (fun (n : ℕ) (z : SpaceTime × (Velocity × Velocity)) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) 1 (μ.prod volume))
    (hg : WeakL1Converges (μ.prod volume) f g)
    (hW : WeakL1Converges (μ.prod volume)
      (fun n z => f n (z.1,z.2.1)*f n (z.1,z.2.2)) W)
    {k l : KineticPhase → ℝ} (hk : Continuous k) (hl : Continuous l)
    (hkc : HasCompactSupport k) (hlc : HasCompactSupport l)
    {A B : SpaceTime → ℝ}
    (hA : TimeLocalL1Converges T (fun n x => ∫ v, k (x,v)*f n (x,v)) A)
    (hB : TimeLocalL1Converges T (fun n x => ∫ v, l (x,v)*f n (x,v)) B)
    {K : Set SpaceTime} (hK : IsCompact K) [IsFiniteMeasure (μ.restrict K)] :
    (fun x => ∫ y : Velocity × Velocity, (k (x,y.1)*l (x,y.2))*W (x,y)) =ᵐ[μ.restrict K]
      (fun x => (∫ v, k (x,v)*g (x,v))*(∫ w, l (x,w)*g (x,w))) := by
  have hμv : μ ≤ (volume : Measure SpaceTime) := hμ.trans
    (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hmK := Measure.restrict_mono_measure hμ K
  have hAi := (hA.1.integrableOn_isCompact hK).mono_measure hμv
  have hBi := (hB.1.integrableOn_isCompact hK).mono_measure hμv
  have hA' : Tendsto (fun n => eLpNorm (fun x => (∫ v, k (x,v)*f n (x,v))-A x) 1
      (μ.restrict K)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hA.2 K hK)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ hmK)
  have hB' : Tendsto (fun n => eLpNorm (fun x => (∫ v, l (x,v)*f n (x,v))-B x) 1
      (μ.restrict K)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hB.2 K hK)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ hmK)
  have hfK (n) : Integrable (f n) ((μ.restrict K).prod volume) := by
    exact (hfi n).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hpK (n) : Integrable (fun z : SpaceTime × (Velocity × Velocity) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) ((μ.restrict K).prod (volume.prod volume)) := by
    have hi : Integrable (fun z : SpaceTime × (Velocity × Velocity) =>
        f n (z.1,z.2.1)*f n (z.1,z.2.2))
        ((μ.restrict K).prod (volume : Measure (Velocity × Velocity))) :=
      (memLp_one_iff_integrable.mp (hpUI.memLp n)).mono_measure
        (Measure.prod_mono Measure.restrict_le_self le_rfl)
    simpa only [Measure.volume_eq_prod] using hi
  have hgK := hg.restrict_base hK.measurableSet
  have hWK := hW.restrict_base hK.measurableSet
  rw [Measure.volume_eq_prod] at hWK
  obtain ⟨C,hC⟩ := hk.bounded_above_of_compact_support hkc
  obtain ⟨D,hD⟩ := hl.bounded_above_of_compact_support hlc
  have hui := Compactness.uniformIntegrable_restrict
    (Compactness.uniformIntegrable_compact_average_product hfm hpUI hk hl hkc hlc) K
  have he := weak_pair_moment_factorization hfm hfK hpK hgK hWK hk.measurable hl.measurable
    C D hC hD hAi hBi hA' hB' hui
  simpa only [← Measure.volume_eq_prod] using he

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakCapOuterBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual weak density and pair-product limits of the cap approximations

The equality of the pair limit with the product of density limits is the
subsequent velocity-averaging step, not an assumption of this extraction.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

private theorem uniformIntegrable_comp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} (hf : UniformIntegrable f 1 μ) (a : ℕ → ℕ) :
    UniformIntegrable (fun n => f (a n)) 1 μ := by
  obtain ⟨hu,C,hC⟩ := hf
  exact ⟨hu.comp a,C,fun n => hC (a n)⟩

theorem TightCapFamily.exists_weak_limits (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value)) W ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ W z) := by
  let f := fun N => torusPhysical q (F.approximation N).solution.value
  have hfm (N) : Measurable (f N) :=
    torusPhysical_measurable (F.approximation N).solution.measurable_value q
  have hfn (N) (z) : 0 ≤ f N z :=
    torusPhysical_nonneg (fun u => ((F.approximation N).solution.value_bounds u).1) q z
  have hpairUI := CollisionCompactness.pairProduct_uniformIntegrable hfm hfn F.pairs_ui
  have hpairTight := CollisionCompactness.pairProduct_unifTight hfm hfn F.pairs_tight
  obtain ⟨a,g,ha,hg⟩ := (hDP F.time F.time_pos.le).1 f hfm F.density_ui F.density_tight
  obtain ⟨b,W,hb,hW⟩ := (hDP F.time F.time_pos.le).2
    (fun n => CollisionCompactness.pairProduct (f (a n)))
    (fun n => CollisionCompactness.pairProduct_measurable (hfm (a n)))
    (uniformIntegrable_comp hpairUI a) (hpairTight.comp a)
  have hg' := hg.comp hb.tendsto_atTop
  refine ⟨a ∘ b,g,W,ha.comp hb,hg',hW,?_,?_⟩
  · exact hg'.nonneg (fun n => ae_of_all _ (hfn (a (b n))))
  · exact hW.nonneg (fun n => ae_of_all _ (CollisionCompactness.pairProduct_nonneg (hfn (a (b n)))))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapPairMoments
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local strong convergence of velocity averages of the actual cap solutions -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.averages_resolvent (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) (ψ : Velocity → ℝ) :
    (fun z : Published.SpaceTime => ∫ v, ψ v*(χ (z,v)*EuclideanFlight.density q F.solution.value (z,v)))
      =ᵐ[Published.timeSpaceVolume T]
      Published.resolventAverage (localizedSource T χ (EuclideanFlight.density q F.solution.value)
        (EuclideanFlight.source (N+1) q F.solution.value)) ψ := by
  have hi : Measurable (initial s₀ η K α γ d₀ q N
      (fun p => F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)) :=
    (measurable_seed s₀ η K α γ d₀ q N).add
      ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have hA : 0 < F.amplitude := F.amplitude_pos
  exact EuclideanFlight.velocity_averages_resolvent hcarleman F.solution hq₁ hq₂
    (by positivity) (by positivity) le_rfl hi hχ hzero ψ

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Simultaneous averaging without losing the actual weak density and pair limits -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.countable_physical_averages
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    {s₀ η K α γ d₀ q : ℝ} (F : CompactCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) (a : ℕ → ℕ)
    (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ j (p : Velocity × Velocity), χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, Published.TimeLocalL1Converges F.time (fun n z => ∫ v, ψ j v*
        (χ j (z,v)*EuclideanFlight.density q (F.approximation (a (φ n))).solution.value (z,v)))
        (g j) := by
  have hex (j) : ∃ R : ℝ, 0 < R ∧ tsupport (χ j) ⊆
      {z : Published.KineticPhase | ‖z.2‖ ≤ R} := by
    obtain ⟨R,hR,hball⟩ := ((hc j).image continuous_snd).isBounded.subset_ball_lt 0 (0 : Velocity)
    refine ⟨R,hR,fun z hz => ?_⟩
    have hb := hball (mem_image_of_mem Prod.snd hz)
    exact (by simpa only [Metric.mem_ball,dist_zero_right] using hb : ‖z.2‖ < R).le
  choose R hR hv using hex
  let r : ℕ → ℕ → Published.KineticPhase → ℝ := fun j n => localizedSource F.time (χ j)
    (EuclideanFlight.density q (F.approximation (a n)).solution.value)
    (EuclideanFlight.source (a n+1) q (F.approximation (a n)).solution.value)
  have hr (j n) : ∀ᵐ z ∂(volume : Measure Published.KineticPhase), R j < ‖z.2‖ → r j n z = 0 :=
    ae_of_all _ (fun z hz => localizedSource_velocity_support (hv j) _ _ z hz)
  have hui (j) : UniformIntegrable (r j) 1 volume :=
    Compactness.uniformIntegrable_comp (F.localized_source_ui (hχ j) (hc j) (hs j)) a
  obtain ⟨φ,g,hφ,hg⟩ := hGLPS.countable_sources_tests r R hR hr hui ψ hψ hψc
  refine ⟨φ,g,hφ,fun j => (hg j).time_restrict (fun n => ?_)⟩
  exact (F.approximation (a (φ n))).averages_resolvent hcarleman hq₁ hq₂ (hχ j) (hzero j) (ψ j)

theorem TightCapFamily.exists_weak_and_average_limits
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ j (p : Velocity × Velocity), χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ)
      (A : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value)) W ∧
      (∀ j, Published.TimeLocalL1Converges F.time (fun n z => ∫ v, ψ j v*
        (χ j (z,v)*EuclideanFlight.density q (F.approximation (φ n)).solution.value (z,v))) (A j)) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ W z) := by
  obtain ⟨a,g,W,ha,hg,hW,hgn,hWn⟩ := F.exists_weak_limits hDP
  obtain ⟨b,A,hb,hA⟩ := F.toCompactCapFamily.countable_physical_averages hcarleman hGLPS
    hq₁ hq₂ a χ hχ hc hs hzero ψ hψ hψc
  exact ⟨a ∘ b,g,W,A,ha.comp hb,hg.comp hb.tendsto_atTop,hW.comp hb.tendsto_atTop,hA,hgn,hWn⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Factorized velocity-pair moments of actual cap-family weak limits -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_factorized_pair_moments
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ j (p : Velocity × Velocity), χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value)) W ∧
      (∀ i j (S : Set Published.SpaceTime), IsCompact S →
        (fun x => ∫ y : Velocity × Velocity,
          (averageWeight (χ i) (ψ i) (x,y.1)*averageWeight (χ j) (ψ j) (x,y.2))*
            TorusKineticChart.liftPair W (x,y)) =ᵐ[(TorusKineticChart.baseVolume F.time).restrict S]
          (fun x => (∫ v, averageWeight (χ i) (ψ i) (x,v)*TorusKineticChart.liftDensity g (x,v))*
            (∫ w, averageWeight (χ j) (ψ j) (x,w)*TorusKineticChart.liftDensity g (x,w)))) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ W z) := by
  obtain ⟨φ,g,W,A,hφ,hg,hW,hA,hgn,hWn⟩ :=
    F.exists_weak_and_average_limits hcarleman hGLPS hDP hq₁ hq₂ χ hχ hc hs hzero ψ hψ hψc
  refine ⟨φ,g,W,hφ,hg,hW,?_,hgn,hWn⟩
  let f : ℕ → Published.KineticPhase → ℝ := fun n =>
    EuclideanFlight.density q (F.approximation (φ n)).solution.value
  have hfm (n) : Measurable (f n) :=
    EuclideanFlight.density_measurable (F.approximation (φ n)).solution.measurable_value q
  have hfi (n) : Integrable (f n) ((TorusKineticChart.baseVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.toCompactCapFamily.density_ui_cell.memLp (φ n))
  have hpUI := Compactness.uniformIntegrable_comp F.toCompactCapFamily.raw_pairs_ui_cell φ
  have hgw := TorusKineticChart.weak_density_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hg
  have hWw := TorusKineticChart.weak_pair_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hW
  have hkw (j) : Continuous (averageWeight (χ j) (ψ j)) :=
    ((hψ j).continuous.comp continuous_snd).mul (hχ j).continuous
  have hkc (j) : HasCompactSupport (averageWeight (χ j) (ψ j)) := (hc j).mul_left
  have hAw (j) : Published.TimeLocalL1Converges F.time
      (fun n x => ∫ v, averageWeight (χ j) (ψ j) (x,v)*f n (x,v)) (A j) := by
    simpa only [averageWeight,mul_assoc] using hA j
  intro i j S hS
  exact Published.local_pair_moment_factorization (TorusKineticChart.baseVolume_le F.time)
    hfm hfi hpUI hgw hWw (hkw i) (hkw j) (hkc i) (hkc j) (hAw i) (hAw j) hS

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_InteriorCell
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact smooth spacetime cutoffs covering almost all of the physical cell -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.TorusKineticChart

theorem interiorRegion_open : IsOpen interiorRegion := isOpen_Ioi.prod isOpen_interior

theorem cube_convex : Convex ℝ TorusChart.cube := by
  intro x hx y hy a b ha hb hab i
  have hi := (convex_Ioc (-(1/2:ℝ)) (1/2)) (hx i) (hy i) ha hb hab
  simpa only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,TorusChart.interval] using hi

theorem zero_mem_interior_cube : (0 : Velocity) ∈ interior TorusChart.cube := by
  apply mem_interior_iff_mem_nhds.mpr
  have hb : Metric.ball (0 : Velocity) (1/4) ⊆ TorusChart.cube := by
    intro x hx i
    have hxnorm : ‖x‖ < 1/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    have habs : |x i| < 1/4 := hi.trans_lt hxnorm
    have hh := abs_lt.mp habs
    change -(1/2:ℝ) < x i ∧ x i ≤ 1/2
    constructor <;> linarith
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : Velocity) (by norm_num)) hb

theorem interiorRegion_nonempty : interiorRegion.Nonempty :=
  ⟨(1,0),by norm_num [interiorRegion]; exact zero_mem_interior_cube⟩

theorem interior_cube_ae : ∀ᵐ x ∂((volume : Measure Velocity).restrict TorusChart.cube),
    x ∈ interior TorusChart.cube := by
  have hfront := cube_convex.addHaar_frontier (volume : Measure Velocity)
  have hnull : ∀ᵐ x ∂(volume : Measure Velocity), x ∉ frontier TorusChart.cube := by
    apply ae_iff.mpr
    simpa only [Classical.not_not,Set.ofPred_mem_eq] using hfront
  apply (ae_restrict_iff' TorusChart.measurableSet_cube).mpr
  filter_upwards [hnull] with x hx hxc
  by_contra hi
  exact hx ⟨subset_closure hxc,hi⟩

theorem interiorRegion_ae (T : ℝ) : ∀ᵐ z ∂baseVolume T, z ∈ interiorRegion := by
  have ht : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Icc 0 T)), 0 < t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with t ht hn
    exact lt_of_le_of_ne ht.1 (Ne.symm hn)
  exact Measure.ae_prod_iff_ae_ae (interiorRegion_open.measurableSet) |>.mpr
    (ht.mono (fun _ ht => interior_cube_ae.mono (fun _ hx => ⟨ht,hx⟩)))

end BoltzmannNonuniqueness.TorusKineticChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ProductKineticCutoff
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Kinetic cutoffs preserving velocity tests on a spacetime patch -/

noncomputable section

open Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.Compactness

theorem productCutoff_tsupport (χ : Published.SpaceTime → ℝ) (β : Velocity → ℝ) :
    tsupport (productCutoff χ β) ⊆ tsupport χ ×ˢ tsupport β := by
  apply closure_minimal ?_ ((isClosed_tsupport χ).prod (isClosed_tsupport β))
  intro z hz
  have hne := mul_ne_zero_iff.mp hz
  exact ⟨subset_tsupport χ hne.1,subset_tsupport β hne.2⟩

theorem productCutoff_compact {χ : Published.SpaceTime → ℝ} {β : Velocity → ℝ}
    (hχ : HasCompactSupport χ) (hβ : HasCompactSupport β) :
    HasCompactSupport (productCutoff χ β) :=
  (hχ.prod hβ).of_isClosed_subset (isClosed_tsupport _) (productCutoff_tsupport χ β)

theorem productCutoff_smooth {χ : Published.SpaceTime → ℝ} {β : Velocity → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β) :
    ContDiff ℝ (⊤ : ℕ∞) (productCutoff χ β) :=
  (hχ.comp contDiff_fst).mul (hβ.comp contDiff_snd)

theorem productCutoff_in_cell {χ : Published.SpaceTime → ℝ} (β : Velocity → ℝ)
    (hs : tsupport χ ⊆ TorusKineticChart.interiorRegion) :
    tsupport (productCutoff χ β) ⊆ {z | z.1.2 ∈ TorusChart.cube} := by
  intro z hz
  change z.1.2 ∈ TorusChart.cube
  exact interior_subset (hs ((productCutoff_tsupport χ β hz).1)).2

theorem productCutoff_initial_zero {χ : Published.SpaceTime → ℝ} (β : Velocity → ℝ)
    (hs : tsupport χ ⊆ TorusKineticChart.interiorRegion) (p : Velocity × Velocity) :
    productCutoff χ β (characteristic p 0) = 0 := by
  have hn : (0,p.1) ∉ tsupport χ := fun h => lt_irrefl (0 : ℝ) (hs h).1
  have hz := image_eq_zero_of_notMem_tsupport hn
  simp only [productCutoff,characteristic,zero_smul,add_zero,hz,zero_mul]

theorem productCutoff_preserves_test (χ : Published.SpaceTime → ℝ)
    {β ψ : Velocity → ℝ} (hβ : ∀ v, ψ v*β v = ψ v) :
    JetCopyDatum.averageWeight (productCutoff χ β) ψ = fun z => χ z.1*ψ z.2 := by
  funext z
  change ψ z.2*(χ z.1*β z.2) = χ z.1*ψ z.2
  calc
    _ = χ z.1*(ψ z.2*β z.2) := by ring
    _ = _ := by rw [hβ]

end BoltzmannNonuniqueness.Compactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapWeightedNonlinearLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Identification of the actual cap-family weak pair limit -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

/-- The velocity-averaging step identifies the genuine nonlinear pair product. -/
theorem TightCapFamily.exists_nonlinear_weak_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairProduct g) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) := by
  obtain ⟨ψ,hψ,hψc,hdet⟩ := Compactness.exists_countable_smooth_determining_tests
  choose β hβ hβc _hβn hβtest using fun i => Compactness.exists_velocity_cutoff (hψc i)
  obtain ⟨χ,hχ,hχc,hχs,hcover⟩ := Compactness.exists_spacetime_cutoff_cover
    TorusKineticChart.interiorRegion_open TorusKineticChart.interiorRegion_nonempty
  let cuts : ℕ → Published.KineticPhase → ℝ := fun n =>
    Compactness.productCutoff (χ (Nat.unpair n).1) (β (Nat.unpair n).2)
  let tests : ℕ → Velocity → ℝ := fun n => ψ (Nat.unpair n).2
  have hcuts (n) : ContDiff ℝ (⊤ : ℕ∞) (cuts n) :=
    Compactness.productCutoff_smooth (hχ _) (hβ _)
  have hcutsc (n) : HasCompactSupport (cuts n) :=
    Compactness.productCutoff_compact (hχc _) (hβc _)
  have hcutss (n) : tsupport (cuts n) ⊆ {z | z.1.2 ∈ TorusChart.cube} :=
    Compactness.productCutoff_in_cell _ (hχs _)
  have hcuts0 (n) (p : Velocity × Velocity) : cuts n (TransportCutoff.characteristic p 0) = 0 :=
    Compactness.productCutoff_initial_zero _ (hχs _) p
  obtain ⟨φ,g,W,hφ,hg,hW,hmom,hgn,_hWn⟩ := F.exists_factorized_pair_moments
    hcarleman hGLPS hDP hq₁ hq₂ cuts hcuts hcutsc hcutss hcuts0 tests
    (fun n => hψ _) (fun n => hψc _)
  have hw (s i : ℕ) : averageWeight (cuts (Nat.pair s i)) (tests (Nat.pair s i)) =
      fun z => χ s z.1*ψ i z.2 := by
    dsimp only [cuts,tests]
    rw [Nat.unpair_pair]
    exact Compactness.productCutoff_preserves_test (χ s) (hβtest i)
  have hgw := TorusKineticChart.weak_density_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hg
  have hWw := TorusKineticChart.weak_pair_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hW
  have hscaled (s i j : ℕ) : ∀ᵐ x ∂TorusKineticChart.baseVolume F.time,
      (∫ y : Velocity × Velocity, ((χ s x*ψ i y.1)*(χ s x*ψ j y.2))*TorusKineticChart.liftPair W (x,y)) =
        (∫ v, (χ s x*ψ i v)*TorusKineticChart.liftDensity g (x,v))*
          (∫ w, (χ s x*ψ j w)*TorusKineticChart.liftDensity g (x,w)) := by
    apply Compactness.ae_of_all_compact_restrict
    intro S hS
    have ht := hmom (Nat.pair s i) (Nat.pair s j) S hS
    simp only [hw s i,hw s j] at ht
    filter_upwards [ht] with x hx
    exact hx
  have hpatch (s) : ∀ᵐ x ∂TorusKineticChart.baseVolume F.time, χ s x ≠ 0 →
      (fun y => TorusKineticChart.liftPair W (x,y)) =ᵐ[volume]
        (fun y : Velocity × Velocity => TorusKineticChart.liftDensity g (x,y.1)*
          TorusKineticChart.liftDensity g (x,y.2)) := by
    apply Compactness.pair_identity_on_patch hψ hψc hdet hWw.1 hgw.1 hWw.2.1 hgw.2.1 (χ s)
    exact fun i j => (hscaled s i j).mono (fun _ h _ => h)
  have hfib : ∀ᵐ x ∂TorusKineticChart.baseVolume F.time,
      (fun y => TorusKineticChart.liftPair W (x,y)) =ᵐ[volume]
        (fun y : Velocity × Velocity => TorusKineticChart.liftDensity g (x,y.1)*
          TorusKineticChart.liftDensity g (x,y.2)) := by
    filter_upwards [ae_all_iff.mpr hpatch,TorusKineticChart.interiorRegion_ae F.time] with x hx hxin
    obtain ⟨s,hs⟩ := hcover x hxin
    exact hx s hs
  have he : TorusKineticChart.liftPair W =ᵐ[TorusKineticChart.pairCellVolume F.time]
      CollisionCompactness.pairProduct (TorusKineticChart.liftDensity g) := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr hfib
    exact measurableSet_eq_fun hWw.1 (CollisionCompactness.pairProduct_measurable hgw.1)
  have hback := (TorusKineticChart.pair_measurePreserving F.time).quasiMeasurePreserving.ae he
  have hEq : W =ᵐ[(AnnularEnvelope.timePositionVolume F.time).prod volume]
      CollisionCompactness.pairProduct g := by
    filter_upwards [hback] with z hz
    simpa only [TorusKineticChart.liftPair,TorusKineticChart.pairChart,
      CollisionCompactness.pairProduct,TorusKineticChart.liftDensity,
      TorusChart.projection_representative] using hz
  refine ⟨φ,g,hφ,hg,?_,hgn⟩
  refine ⟨CollisionCompactness.pairProduct_measurable hg.1,hW.2.1.congr hEq,?_⟩
  intro θ hθ hθB
  have ht := hW.2.2 θ hθ hθB
  have hi : (∫ z, θ z*W z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume) =
      ∫ z, θ z*CollisionCompactness.pairProduct g z
        ∂(AnnularEnvelope.timePositionVolume F.time).prod volume :=
    integral_congr_ae (hEq.mono (fun z hz => congrArg (fun y => θ z*y) hz))
  rw [hi] at ht
  exact ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The physical pair weight also converges to the genuine nonlinear product -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_weighted_nonlinear_weak_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) := by
  obtain ⟨a,g,ha,hg,hraw,hgn⟩ := F.exists_nonlinear_weak_limit hcarleman hGLPS hDP hq₁ hq₂
  have hm (n) := CollisionCompactness.pairDensity_measurable
    (torusPhysical_measurable (F.approximation (a n)).solution.measurable_value q)
  obtain ⟨b,G,hb,hG⟩ := (hDP F.time F.time_pos.le).2
    (fun n => CollisionCompactness.pairDensity (torusPhysical q (F.approximation (a n)).solution.value))
    hm (Compactness.uniformIntegrable_comp F.pairs_ui a) (F.pairs_tight.comp a)
  let w : (ℝ × Position) × (Velocity × Velocity) → ℝ := fun z => 1+‖z.2.1‖+‖z.2.2‖
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hw1 : ∀ z, 1 ≤ w z := by
    intro z
    dsimp [w]
    linarith [norm_nonneg z.2.1,norm_nonneg z.2.2]
  have hfun (u : (ℝ × Position) × Velocity → ℝ) :
      (fun z => w z*CollisionCompactness.pairProduct u z) = CollisionCompactness.pairDensity u := by
    funext z
    simp only [w,CollisionCompactness.pairProduct,CollisionCompactness.pairDensity,mul_assoc]
  have hraw' := hraw.comp hb.tendsto_atTop
  have hG' : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n z => w z*CollisionCompactness.pairProduct
        (torusPhysical q (F.approximation (a (b n))).solution.value) z) G := by
    have hseq : (fun n z => w z*CollisionCompactness.pairProduct
        (torusPhysical q (F.approximation (a (b n))).solution.value) z) =
        (fun n => CollisionCompactness.pairDensity (torusPhysical q
          (F.approximation (a (b n))).solution.value)) := funext (fun n => hfun _)
    rw [hseq]
    exact hG
  have he := Published.identify_weighted_weak_limit hraw' hG' hw hw1
  have he' : G =ᵐ[(AnnularEnvelope.timePositionVolume F.time).prod volume]
      CollisionCompactness.pairDensity g := by
    rw [hfun] at he
    exact he
  exact ⟨a ∘ b,g,ha.comp hb,hg.comp hb.tendsto_atTop,
    hG.congr_limit (CollisionCompactness.pairDensity_measurable hg.1) he',hgn⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveNonlinearLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A nonnegative representative of the actual weighted nonlinear weak limit -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_positive_nonlinear_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧ (∀ z, 0 ≤ g z) := by
  obtain ⟨φ,g,hφ,hg,hpair,hgn⟩ := F.exists_weighted_nonlinear_weak_limit hcarleman hGLPS hDP hq₁ hq₂
  let g' : (ℝ × Position) × Velocity → ℝ := fun z => max (g z) 0
  have hm : Measurable g' := hg.1.max measurable_const
  have he : g =ᵐ[(AnnularEnvelope.timePositionVolume F.time).prod volume] g' := by
    filter_upwards [hgn] with z hz
    exact (max_eq_left hz).symm
  have hpe := CollisionCompactness.pairDensity_congr hg.1 hm he
  exact ⟨φ,g',hφ,hg.congr_limit hm he,
    hpair.congr_limit (CollisionCompactness.pairDensity_measurable hm) hpe,
    fun z => le_max_right _ _⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticWindowL1
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Regrouping time and phase space in the weak limit -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

theorem weak_regroup {μ : Measure ℝ} [SFinite μ]
    {f : ℕ → (ℝ × Position) × Velocity → ℝ} {g : (ℝ × Position) × Velocity → ℝ}
    (hf : ∀ n, Measurable (f n))
    (h : Published.WeakL1Converges ((μ.prod volume).prod volume) f g) :
    Published.WeakL1Converges (μ.prod (volume : Measure Phase))
      (fun n => regroup (f n)) (regroup g) := by
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((ℝ × Position) × Velocity) ≃ᵐ ℝ × Phase)
      ((μ.prod volume).prod volume) (μ.prod volume) := by
    simpa only [Measure.volume_eq_prod] using measurePreserving_prodAssoc μ
      (volume : Measure Position) (volume : Measure Velocity)
  exact Published.WeakL1Converges.of_comp_measurePreserving hmp
    (fun n => (hf n).comp MeasurableEquiv.prodAssoc.symm.measurable)
    (h.1.comp MeasurableEquiv.prodAssoc.symm.measurable) h

theorem weak_constant_time {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℕ → Phase → ℝ} {g : Phase → ℝ} (hf : ∀ n, Measurable (f n))
    (hfi : ∀ n, Integrable (f n)) (h : Published.WeakL1Converges volume f g) :
    Published.WeakL1Converges (μ.prod volume) (fun n z => f n z.2) (fun z => g z.2) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving
    (Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ))
    (fun n => (hf n).comp measurable_snd) (h.1.comp measurable_snd)
  exact h.prod_constant hfi

end BoltzmannNonuniqueness.TorusFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakDuhamelLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing the characteristic initial-value identity through the weak limits -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

theorem weak_duhamel_limit {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f r : ℕ → ℝ × Phase → ℝ} {g R : ℝ × Phase → ℝ}
    {a : ℕ → Phase → ℝ} {a₀ : Phase → ℝ}
    (hf : Published.WeakL1Converges (μ.prod volume) f g)
    (hr : Published.WeakL1Converges (μ.prod volume) r R)
    (hrm : ∀ n, Measurable (r n)) (hri : ∀ n, Integrable (r n) (μ.prod volume))
    (ha : Published.WeakL1Converges volume a a₀)
    (ham : ∀ n, Measurable (a n)) (hai : ∀ n, Integrable (a n))
    (heq : ∀ n, f n =ᵐ[μ.prod volume]
      (fun z => a n z.2+Published.timePrimitive μ (r n) z)) :
    g =ᵐ[μ.prod volume] (fun z => a₀ z.2+Published.timePrimitive μ R z) := by
  have hinit := weak_constant_time ham hai ha (μ := μ)
  have hprim := hr.timePrimitive hrm hri
  have hsum := hinit.add hprim
    (fun n => (hai n).comp_snd μ)
    (fun n => Published.timePrimitive_integrable (hrm n) (hri n))
  exact hf.unique (hsum.congr_sequence (fun n => (heq n).symm))

end BoltzmannNonuniqueness.TorusFlight

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

/-! # The actual periodic approximations satisfy a spacetime mild identity -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusFlight

theorem initialDensity_measurable {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀) (q : ℝ) :
    Measurable (initialDensity q f₀) := by
  have hp : Measurable JetPeriodicDatum.phaseMap := by
    convert EuclideanFlight.phaseEquiv.measurable using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact (EuclideanFlight.phaseEquiv_apply p).symm
  exact ((ChartKernel.measurable_H q).comp measurable_snd).mul
    (hf₀.comp (hp.comp TorusChart.phase_measurePreserving.measurable))

theorem spacetime_mild (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (_hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀) :
    along (regroup (JetCopyDatum.torusPhysical q F.value)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => initialDensity q f₀ z.2 +
      Published.timePrimitive (volume.restrict (Icc 0 T))
        (along (regroup (CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F.value)))) z) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hm := JetCopyDatum.torusPhysical_measurable F.measurable_value q
  have hrm := CollisionCompactness.collisionSource_measurable hm b
  have hreg : Measurable (regroup (JetCopyDatum.torusPhysical q F.value)) :=
    hm.comp MeasurableEquiv.prodAssoc.symm.measurable
  have hsr : Measurable (regroup (CollisionCompactness.collisionSource b
      (JetCopyDatum.torusPhysical q F.value))) := hrm.comp MeasurableEquiv.prodAssoc.symm.measurable
  have hAm := hreg.comp (along_measurePreserving μ).measurable
  have hBm := ((initialDensity_measurable hf₀ q).comp measurable_snd).add
    (Published.timePrimitive_measurable μ (hsr.comp (along_measurePreserving μ).measurable))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hAm hBm)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have h := characteristic hcarleman F hq₁ hq₂ hb hR ht.1 (ht.2.trans hTU) hloss hf₀
  filter_upwards [h] with p hp
  change along (regroup (JetCopyDatum.torusPhysical q F.value)) (t,p) =
    initialDensity q f₀ p + Published.timePrimitive (volume.restrict (Icc 0 T))
      (along (regroup (CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F.value)))) (t,p)
  rw [Published.timePrimitive_eq_interval ht]
  exact hp

end BoltzmannNonuniqueness.TorusFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapMildLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Convergence of the actual right-hand sides of the cap equations -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_cutoff_equation_limit_with_pair
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.collisionSource (φ n+1)
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p) ∧
      Integrable (CollisionCompactness.pairDensity g)
        ((AnnularEnvelope.timePositionVolume F.time).prod volume) ∧ (∀ z, 0 ≤ g z) ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) := by
  obtain ⟨φ,g,hφ,hg,hpair,hgn⟩ := F.exists_positive_nonlinear_limit hcarleman hGLPS hDP hq₁ hq₂
  have hfm n := torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hfn n := torusPhysical_nonneg
    (fun z => ((F.approximation (φ n)).solution.value_bounds z).1) q
  have hf n := memLp_one_iff_integrable.mp (F.pairs_ui.memLp (φ n))
  have hb : Tendsto (fun n => (φ n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n, (φ n : ℝ) ≤ (φ n : ℝ)+1)
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hterms := CollisionCompactness.weak_cutoff_gainLoss hfm hfn hg.1 hpair hf hb
  have hdiff := hterms.1.sub hterms.2
    (fun n => memLp_one_iff_integrable.mp (F.gain_ui.memLp (φ n)))
    (fun n => memLp_one_iff_integrable.mp (F.loss_ui.memLp (φ n)))
  have he n : (fun p => KineticCollisionNullSets.gain (φ n+1)
      (torusPhysical q (F.approximation (φ n)).solution.value) p-
      CollisionCompactness.cutoffLossDensity (φ n+1)
        (torusPhysical q (F.approximation (φ n)).solution.value) p) =ᵐ[
        (AnnularEnvelope.timePositionVolume F.time).prod volume]
      CollisionCompactness.collisionSource (φ n+1)
        (torusPhysical q (F.approximation (φ n)).solution.value) := by
    filter_upwards [CollisionCompactness.cutoff_loss_ae_eq_frequency (hfm n) (hfn n) (hf n)
      (φ n+1)] with p hp
    simp only [CollisionCompactness.collisionSource,hp]
  exact ⟨φ,g,hφ,hg,hdiff.congr_sequence he,hpair.2.1,hgn,hpair⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The cap approximations satisfy the actual torus initial-value identity -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem periodicInitial_measurable (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (ell : ℝ) :
    Measurable (periodicInitial s₀ η K α γ d₀ q N ell) := by
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul ell)
  have he : periodicInitial s₀ η K α γ d₀ q N ell =
      TorusFlight.initialDensity q (initial s₀ η K α γ d₀ q N
        (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)) := by
    funext p
    exact mul_comm _ _
  rw [he]
  exact TorusFlight.initialDensity_measurable hm q

theorem CapApproximation.spacetime_mild (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) :
    TorusFlight.along (TorusFlight.regroup (torusPhysical q F.solution.value)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => periodicInitial s₀ η K α γ d₀ q N F.coefficient z.2 +
      Published.timePrimitive (volume.restrict (Icc 0 T))
        (TorusFlight.along (TorusFlight.regroup
          (CollisionCompactness.collisionSource (N+1) (torusPhysical q F.solution.value)))) z) := by
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have h := TorusFlight.spacetime_mild hcarleman F.solution hq₁ hq₂
    (by positivity) (by have := F.amplitude_pos; positivity) hT le_rfl le_rfl hm
  filter_upwards [h] with z hz
  convert hz using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  exact mul_comm _ _

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual cap initial data converge weakly to the prescribed cold datum -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem periodicInitial_integrable {s₀ η K γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq : 0 ≤ q) (hqmax : q < 2)
    (α : ℝ) (N : ℕ) (ell : ℝ) :
    Integrable (periodicInitial s₀ η K α γ d₀ q N ell) := by
  have hδ : 0 < DatumBounds.scale s₀ η (N+1) := DatumBounds.scale_pos hs₀ _
  have hδmax : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have he : periodicInitial s₀ η K α γ d₀ q N ell =
      fun p => JetPeriodicDatum.truncated s₀ η K α γ d₀ N p+
        ell*HotSeedProfile.periodicDensity q (DatumBounds.scale s₀ η (N+1)) p :=
    funext (periodicInitial_eq hs₀ hsmax hη hηmax K α γ d₀ q N ell)
  rw [he]
  exact (JetPeriodicDatum.truncated_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α N).add
    ((HotSeedProfile.periodicDensity_integrable hq hqmax hδ hδmax).const_mul ell)

theorem CompactCapFamily.initial_weak_limit {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq : 0 ≤ q) (hqmax : q < 2) :
    Published.WeakL1Converges volume
      (fun n => periodicInitial s₀ η K α γ d₀ q n (F.approximation n).coefficient)
      (JetPeriodicDatum.datum s₀ η K α γ d₀) := by
  have hi := JetPeriodicDatum.integrable_pullback
    (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α)
  exact Published.weakL1_of_integral_norm_sub
    (fun n => periodicInitial_integrable hs₀ hsmax hη hηmax hK hγ hd₀ hq hqmax α n _)
    (JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))) hi F.initial_l1

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A genuine local mild solution obtained from the actual positive cap family -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace JetCopyDatum

theorem TightCapFamily.exists_mild_limit_with_convergence_q80_oai
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.collisionSource (φ n+1)
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p) := by
  obtain ⟨φ,g,hφ,hg,hr,hpair,hgn,hpairweak⟩ := F.exists_cutoff_equation_limit_with_pair hcarleman hGLPS hDP hq₁ hq₂
  let μ : Measure ℝ := volume.restrict (Icc 0 F.time)
  let f : ℕ → (ℝ × Position) × Velocity → ℝ :=
    fun n => torusPhysical q (F.approximation (φ n)).solution.value
  let r : ℕ → (ℝ × Position) × Velocity → ℝ :=
    fun n => CollisionCompactness.collisionSource (φ n+1) (f n)
  let a : ℕ → Phase → ℝ :=
    fun n => periodicInitial s₀ η K α γ d₀ q (φ n) (F.approximation (φ n)).coefficient
  have hfm n : Measurable (f n) :=
    torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hrm n : Measurable (r n) := CollisionCompactness.collisionSource_measurable (hfm n) _
  have hrint n : Integrable (r n) ((AnnularEnvelope.timePositionVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.toCompactCapFamily.source_ui.memLp (φ n))
  have hfr := TorusFlight.weak_regroup hfm hg
  have hrr := TorusFlight.weak_regroup hrm hr
  have hfa := TorusFlight.weak_along
    (fun n => (hfm n).comp MeasurableEquiv.prodAssoc.symm.measurable) hfr
  have hra := TorusFlight.weak_along
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable) hrr
  have hrain n : Integrable (TorusFlight.along (TorusFlight.regroup (r n)))
      (μ.prod (volume : Measure Phase)) := by
    have hrreg : Integrable (TorusFlight.regroup (r n)) (μ.prod (volume : Measure Phase)) := by
      have hi := (measurePreserving_prodAssoc μ (volume : Measure Position)
        (volume : Measure Velocity)).symm.integrable_comp_of_integrable (hrint n)
      rw [Measure.volume_eq_prod]
      exact hi
    exact (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hrreg
  have ham n : Measurable (a n) := periodicInitial_measurable s₀ η K α γ d₀ q _ _
  have hai n : Integrable (a n) := periodicInitial_integrable hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂ α _ _
  have ha := (F.toCompactCapFamily.initial_weak_limit hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂).comp hφ.tendsto_atTop
  have heq n : TorusFlight.along (TorusFlight.regroup (f n)) =ᵐ[μ.prod volume]
      (fun z => a n z.2+Published.timePrimitive μ
        (TorusFlight.along (TorusFlight.regroup (r n))) z) :=
    (F.approximation (φ n)).spacetime_mild hcarleman hq₁ hq₂ F.time_pos.le
  have hlim := TorusFlight.weak_duhamel_limit hfa hra
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable |>.comp
      (TorusFlight.along_measurePreserving μ).measurable)
    hrain ha ham hai heq
  exact ⟨φ,g,hφ,hg,⟨hg.1,hgn,hg.2.1,hpair,hlim⟩,hpairweak,hr⟩

end JetCopyDatum
end BoltzmannNonuniqueness

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_convergence_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_convergence_q80_oai
