-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_traces_and_convergence_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:44:08.368026+00:00
-- url     : https://prove2.me/submissions/4ecf62d6-9580-4f45-9165-e91fdc4a6597

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_HotRepresentative_ae_good_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_TightCapFamily_exists_mild_limit_with_convergence_q80

section
-- module Solutions.OAIQ080_BZ.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

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

/-! ### `UnifIntegrable` -/

namespace UnifIntegrable

protected theorem sub (hf : UnifIntegrable f p μ) (hg : UnifIntegrable g p μ) (hp : 1 ≤ p) :
    UnifIntegrable (f - g) p μ :=
  ⟨hf.1.sub hg.1 hp hf.2 hg.2, fun i => (hf.2 i).sub (hg.2 i)⟩

end UnifIntegrable

/-! ### `UniformIntegrable` -/

namespace UniformIntegrable

protected theorem memLp (hf : UniformIntegrable f p μ) (i : ι) : MemLp (f i) p μ :=
  (uniformIntegrable_iff_mathlib.1 hf).memLp i

theorem toMathlib (hf : UniformIntegrable f p μ) : MeasureTheory.UniformIntegrable f p μ :=
  uniformIntegrable_iff_mathlib.1 hf

theorem ae_eq (hf : UniformIntegrable f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UniformIntegrable g p μ :=
  uniformIntegrable_iff_mathlib.2 (hf.toMathlib.ae_eq hfg)

end UniformIntegrable


/-! ### `UnifTight` -/

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1Operations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem source_eq_collision (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    source b q F = CollisionCompactness.collisionSource b (density q F) := by
  funext z
  rfl

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakTimeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The characteristic primitive converges weakly at every fixed time -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.timePrimitive_slice {μ : Measure ℝ} {ν : Measure X}
    [SFinite μ] [SFinite ν] {f : ℕ → ℝ × X → ℝ} {g : ℝ × X → ℝ}
    (h : WeakL1Converges (μ.prod ν) f g) (hfm : ∀ n, Measurable (f n))
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) (t : ℝ) :
    WeakL1Converges ν (fun n x => Published.timePrimitive μ (f n) (t,x))
      (fun x => Published.timePrimitive μ g (t,x)) := by
  have hs : WeakL1Converges (ν.prod μ) (fun n p => f n p.swap) (fun p => g p.swap) := by
    apply WeakL1Converges.of_comp_measurePreserving
      (Measure.measurePreserving_swap (μ := μ) (ν := ν))
      (fun n => (hfm n).comp measurable_swap) (h.1.comp measurable_swap)
    exact h
  have hi n : Integrable (fun p : X × ℝ => f n p.swap) (ν.prod μ) :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).integrable_comp_of_integrable (hfi n)
  let k : X × ℝ → ℝ := fun p => if p.2 ≤ t then 1 else 0
  have hk : Measurable k := measurable_const.ite
    (measurableSet_le measurable_snd measurable_const) measurable_const
  have hb : ∀ p, |k p| ≤ 1 := by intro p; dsimp [k]; split <;> norm_num
  have hh := hs.marginal hi hk 1 hb
  simpa only [k,Published.timePrimitive,ite_mul,one_mul,zero_mul,Prod.swap_prod_mk] using hh

theorem timePrimitive_slice_integrable {μ : Measure ℝ} {ν : Measure X}
    [SFinite μ] [SFinite ν] {f : ℝ × X → ℝ}
    (hfm : Measurable f) (hfi : Integrable f (μ.prod ν)) (t : ℝ) :
    Integrable (fun x => Published.timePrimitive μ f (t,x)) ν := by
  have h : WeakL1Converges (μ.prod ν) (fun _ : ℕ => f) f :=
    ⟨hfm,hfi,fun _ _ _ => tendsto_const_nhds⟩
  exact (h.timePrimitive_slice (fun _ => hfm) (fun _ => hfi) t).2.1

theorem WeakL1Converges.mild_slice {μ : Measure ℝ} {ν : Measure X}
    [SFinite μ] [SFinite ν] {r : ℕ → ℝ × X → ℝ} {R : ℝ × X → ℝ}
    {a : ℕ → X → ℝ} {a₀ : X → ℝ}
    (ha : WeakL1Converges ν a a₀) (hai : ∀ n, Integrable (a n) ν)
    (hr : WeakL1Converges (μ.prod ν) r R)
    (hrm : ∀ n, Measurable (r n)) (hri : ∀ n, Integrable (r n) (μ.prod ν)) (t : ℝ) :
    WeakL1Converges ν (fun n x => a n x+Published.timePrimitive μ (r n) (t,x))
      (fun x => a₀ x+Published.timePrimitive μ R (t,x)) :=
  ha.add (hr.timePrimitive_slice hrm hri t) hai
    (fun n => timePrimitive_slice_integrable (hrm n) (hri n) t)

end BoltzmannNonuniqueness.Published

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakEntropyMarginal
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Every-time weak convergence of actual characteristic solutions -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.TorusFlight

theorem weak_of_characteristic_slice {μ : Measure ℝ} [IsFiniteMeasure μ]
    {r : ℕ → ℝ × Phase → ℝ} {R : ℝ × Phase → ℝ}
    {a : ℕ → Density} {a₀ : Density} {u : ℕ → Density}
    (ha : Published.WeakL1Converges volume a a₀) (hai : ∀ n, Integrable (a n))
    (hr : Published.WeakL1Converges (μ.prod volume) r R)
    (hrm : ∀ n, Measurable (r n)) (hri : ∀ n, Integrable (r n) (μ.prod volume))
    (t : ℝ) (hum : ∀ n, Measurable (u n))
    (he : ∀ n, (fun p => u n (flight t p)) =ᵐ[volume]
      characteristicProfile μ (a n) (r n) t) :
    Published.WeakL1Converges volume u (eulerianProfile μ a₀ R t) := by
  have hp := ha.mild_slice hai hr hrm hri t
  have hh := hp.congr_sequence (fun n => (he n).symm)
  apply Published.WeakL1Converges.of_comp_measurePreserving (flight_measurePreserving t) hum
    (hp.1.comp (flight_measurePreserving (-t)).measurable)
  simpa only [eulerianProfile,characteristicProfile,Function.comp_def,flight_neg] using hh

end BoltzmannNonuniqueness.TorusFlight

end

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

end BoltzmannNonuniqueness.TorusKineticChart

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

/-! # Every-time characteristic traces of the finite cap approximations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.characteristic_slice (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun p => torusPhysical q F.solution.value
      ((t,(TorusFlight.flight t p).1),(TorusFlight.flight t p).2)) =ᵐ[volume]
    TorusFlight.characteristicProfile (volume.restrict (Icc 0 T))
      (periodicInitial s₀ η K α γ d₀ q N F.coefficient)
      (TorusFlight.along (TorusFlight.regroup
        (CollisionCompactness.collisionSource (N+1) (torusPhysical q F.solution.value)))) t := by
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have h := TorusFlight.characteristic hcarleman F.solution hq₁ hq₂
    (by positivity) (by have := F.amplitude_pos; positivity) ht.1 ht.2 le_rfl hm
  filter_upwards [h] with p hp
  change _ = periodicInitial s₀ η K α γ d₀ q N F.coefficient p+
    Published.timePrimitive (volume.restrict (Icc 0 T)) _ (t,p)
  rw [Published.timePrimitive_eq_interval ht]
  convert hp using 1
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

theorem positiveEvolution_eq_ae (S : MildCollisionSolution T f₀ g) :
    TorusFlight.regroup g =ᵐ[(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
      (fun z => positiveEvolution T f₀ g z.1 z.2) := by
  filter_upwards [S.evolution_eq_ae] with z hz
  change TorusFlight.regroup g z = max (evolution T f₀ g z.1 z.2) 0
  rw [← hz]
  exact (max_eq_left (S.nonnegative ((z.1,z.2.1),z.2.2))).symm

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

/-! # Weak kinetic traces for a fixed nonlinear mild limit -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

theorem weak_kinetic_trace {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    {u r : ℕ → (ℝ × Position) × Velocity → ℝ} {a : ℕ → Density}
    (hum : ∀ n, Measurable (u n)) (hrm : ∀ n, Measurable (r n))
    (hri : ∀ n, Integrable (r n) ((AnnularEnvelope.timePositionVolume T).prod volume))
    (ha : Published.WeakL1Converges volume a f₀) (hai : ∀ n, Integrable (a n))
    (hr : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume T).prod volume) r (source g))
    (t : ℝ) (ht : t ∈ Icc 0 T)
    (hchar : ∀ n, (fun p => u n ((t,(TorusFlight.flight t p).1),(TorusFlight.flight t p).2)) =ᵐ[volume]
      TorusFlight.characteristicProfile (volume.restrict (Icc 0 T)) (a n)
        (TorusFlight.along (TorusFlight.regroup (r n))) t) :
    Published.WeakL1Converges volume (fun n p => u n ((t,p.1),p.2)) (positiveEvolution T f₀ g t) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hrr := TorusFlight.weak_regroup hrm hr
  have hra := TorusFlight.weak_along
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable) hrr
  have hrain n : Integrable (TorusFlight.along (TorusFlight.regroup (r n)))
      (μ.prod (volume : Measure Phase)) := by
    have hi := (measurePreserving_prodAssoc μ (volume : Measure Position)
      (volume : Measure Velocity)).symm.integrable_comp_of_integrable (hri n)
    rw [Measure.volume_eq_prod] at ⊢
    exact (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hi
  have hw := TorusFlight.weak_of_characteristic_slice ha hai hra
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable |>.comp
      (TorusFlight.along_measurePreserving μ).measurable)
    hrain t (fun n => (hum n).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) hchar
  have hm := S.positiveEvolution_measurable ha.1
  exact hw.congr_limit (hm.comp (measurable_const.prodMk measurable_id))
    (S.evolution_eq_positive_each_time hT ha.1 ha.2.1 t ht)

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapEntropyMoments
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Every-time weak traces for the same cap subsequence as the nonlinear mild limit -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.weak_each_time
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ} (hφ : StrictMono φ)
    (S : MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g)
    (hr : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => CollisionCompactness.collisionSource (φ n+1)
        (torusPhysical q (F.approximation (φ n)).solution.value))
      (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p))
    {t : ℝ} (ht : t ∈ Icc 0 F.time) :
    Published.WeakL1Converges volume
      (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
      (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t) := by
  let r : ℕ → (ℝ × Position) × Velocity → ℝ := fun n =>
    CollisionCompactness.collisionSource (φ n+1) (torusPhysical q (F.approximation (φ n)).solution.value)
  let a : ℕ → Density := fun n => periodicInitial s₀ η K α γ d₀ q (φ n)
    (F.approximation (φ n)).coefficient
  have hfm n := torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hrm n : Measurable (r n) := CollisionCompactness.collisionSource_measurable (hfm n) _
  have hri n : Integrable (r n) ((AnnularEnvelope.timePositionVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.toCompactCapFamily.source_ui.memLp (φ n))
  have ha := (F.toCompactCapFamily.initial_weak_limit hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂).comp hφ.tendsto_atTop
  have hai n : Integrable (a n) := periodicInitial_integrable hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂ α _ _
  exact S.weak_kinetic_trace F.time_pos hfm hrm hri ha hai hr t ht
    (fun n => (F.approximation (φ n)).characteristic_slice hcarleman hq₁ hq₂ ht)

theorem TightCapFamily.exists_mild_limit_with_traces_and_convergence_q80_oai
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
      ∀ t ∈ Icc 0 F.time, Published.WeakL1Converges volume
        (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
        (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t) := by
  obtain ⟨φ,g,hφ,hg,S,hpair,hr⟩ := F.exists_mild_limit_with_convergence_q80 hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂
  exact ⟨φ,g,hφ,hg,S,hpair,fun _ ht => F.weak_each_time hcarleman
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂ hφ S hr ht⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_traces_and_convergence_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_traces_and_convergence_q80_oai
