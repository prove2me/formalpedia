-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.entropy_mild_limit_of_convergence_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:28:19.745902+00:00
-- url     : https://prove2.me/submissions/b9524e83-66fe-4349-9eb9-33332818516b

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_HotRepresentative_ae_good_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_bounded_mild_entropy_dissipation_limit_q80

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

/-! ### `UniformIntegrable` -/

namespace UniformIntegrable

protected theorem memLp (hf : UniformIntegrable f p μ) (i : ι) : MemLp (f i) p μ :=
  (uniformIntegrable_iff_mathlib.1 hf).memLp i

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

private theorem one_add_rpow_le {s p : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) :
    (1 + s) ^ p ≤ (2 : ℝ) ^ p * (1 + s ^ p) := by
  by_cases hs₁ : s ≤ 1
  · calc
      (1 + s) ^ p ≤ (2 : ℝ) ^ p :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ ≤ (2 : ℝ) ^ p * (1 + s ^ p) := by
        have hs' : 0 ≤ s ^ p := Real.rpow_nonneg hs p
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ 1 + s ^ p from le_add_of_nonneg_right hs')
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
  · have hs₁' : 1 ≤ s := le_of_lt (lt_of_not_ge hs₁)
    calc
      (1 + s) ^ p ≤ (2 * s) ^ p :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ = (2 : ℝ) ^ p * s ^ p := Real.mul_rpow (by norm_num) hs
      _ ≤ (2 : ℝ) ^ p * (1 + s ^ p) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one)
          (Real.rpow_nonneg (by norm_num) p)

/-- Raising the majorant to a positive power multiplies its transverse singular exponent. -/
theorem H_rpow_le {p : ℝ} (hp : 0 ≤ p) (q : ℝ) (v : Velocity) :
    H q v ^ p ≤ (2 : ℝ) ^ p * gaussianMajorant p (p * q) v := by
  have hs : 0 ≤ singularity q (transverse v) := singularity_nonneg q (transverse v)
  have he : Real.exp (-‖v‖ ^ 2) ^ p = Real.exp (-p * ‖v‖ ^ 2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hr : singularity q (transverse v) ^ p = singularity (p * q) (transverse v) := by
    unfold singularity
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  calc
    H q v ^ p ≤ gaussianMajorant 1 q v ^ p :=
      Real.rpow_le_rpow (H_nonneg q v) (H_le_gaussianMajorant q v) hp
    _ = Real.exp (-p * ‖v‖ ^ 2) * (1 + singularity q (transverse v)) ^ p := by
      unfold gaussianMajorant
      simp only [neg_mul, one_mul]
      rw [Real.mul_rpow (Real.exp_nonneg _) (by positivity), he]
      simp only [neg_mul]
    _ ≤ Real.exp (-p * ‖v‖ ^ 2) *
        ((2 : ℝ) ^ p * (1 + singularity q (transverse v) ^ p)) :=
      mul_le_mul_of_nonneg_left (one_add_rpow_le hs hp) (Real.exp_nonneg _)
    _ = _ := by rw [hr]; unfold gaussianMajorant; ring

/-- The precise power-integrability range used for the initial cutoff solutions. -/
theorem integrable_rpow_H {p q : ℝ} (hp : 1 ≤ p) (hpq : p * q < 2) :
    Integrable (fun v : Velocity => H q v ^ p) := by
  have hp₀ : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_nonneg : 0 ≤ p := hp₀.le
  have hm : AEStronglyMeasurable (fun v : Velocity => H q v ^ p) := by
    unfold H singularity transverse
    fun_prop
  apply ((integrable_gaussianMajorant hp₀ hpq).const_mul ((2 : ℝ) ^ p)).mono' hm
  filter_upwards [] with v
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (H_nonneg q v) p)]
  exact H_rpow_le hp₀.le q v

theorem exists_integrable_rpow_H {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ p : ℝ, 1 < p ∧ Integrable (fun v : Velocity => H q v ^ p) := by
  have hq₀ : 0 < q := lt_trans zero_lt_one hq₁
  have hdiv : (1 : ℝ) < 2 / q := (lt_div_iff₀ hq₀).mpr (by simpa using hq₂)
  obtain ⟨p, hp₁, hp₂⟩ := exists_between hdiv
  exact ⟨p, hp₁, integrable_rpow_H hp₁.le ((lt_div_iff₀ hq₀).mp hp₂)⟩

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

theorem log_scale {s₀ η : ℝ} (hs₀ : 0 < s₀) (j : ℕ) :
    Real.log (scale s₀ η j) = Real.log s₀ - (j : ℝ) * η := by
  rw [scale, Real.log_mul hs₀.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem abs_log_scale_le {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η) (j : ℕ) :
    |Real.log (scale s₀ η j)| ≤ |Real.log s₀| + (j : ℝ) * η := by
  rw [log_scale hs₀]
  calc
    |Real.log s₀ - (j : ℝ) * η| ≤ |Real.log s₀| + |(j : ℝ) * η| := abs_sub _ _
    _ = |Real.log s₀| + (j : ℝ) * η := by
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hη)]

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

/-- A positive scale power also absorbs the absolute logarithm; power four applies to the
vanishing hot-seed entropy estimate in the same datum lemma. -/
theorem summable_scale_pow_log {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (p : ℕ) (hp : 0 < p) :
    Summable (fun j : ℕ => scale s₀ η j ^ p * (1 + |Real.log (scale s₀ η j)|)) := by
  have hindex : Summable (fun j : ℕ => scale s₀ η j ^ p * (j : ℝ)) := by
    simpa only [pow_one] using summable_scale_pow_mul_nat_pow s₀ hη p 1 hp
  have hmajor := ((summable_scale_pow s₀ hη p hp).mul_right (1 + |Real.log s₀|)).add
    (hindex.mul_right η)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hmajor
  · exact mul_nonneg (pow_nonneg (scale_pos (η := η) hs₀ j).le p) (by positivity)
  · have h := mul_le_mul_of_nonneg_left
      (add_le_add_left (abs_log_scale_le hs₀ hη.le j) 1)
      (pow_nonneg (scale_pos (η := η) hs₀ j).le p)
    nlinarith only [h]

theorem summable_entropyBound {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η) :
    Summable (entropyBound s₀ η) := by
  exact summable_scale_pow_log hs₀ hη 2 (by norm_num)

theorem scale_tendsto_zero (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (scale s₀ η) atTop (𝓝 0) := by
  simpa only [pow_one] using (summable_scale_pow s₀ hη 1 (by norm_num)).tendsto_atTop_zero

end BoltzmannNonuniqueness.DatumBounds

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetProfiles
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem J_compact : HasCompactSupport J := bump.hasCompactSupport_normed

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

theorem density_zero {d : ℝ} (hd : 0 < d) (a v : Velocity) (hv : d ≤ ‖v - a‖) :
    density d a v = 0 := by
  have h : 1 ≤ ‖d⁻¹ • (v - a)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    exact (one_le_inv_mul₀ hd).mpr hv
  simp only [density, scaled, J_zero h, mul_zero]

theorem density_velocity_bound {d : ℝ} (hd : 0 < d) {a v : Velocity}
    (hv : density d a v ≠ 0) : ‖v‖ < ‖a‖ + d := by
  have hdist : ‖v - a‖ < d := lt_of_not_ge (fun h => hv (density_zero hd a v h))
  have hnorm := norm_add_le (v - a) a
  rw [sub_add_cancel] at hnorm
  linarith

theorem integrable_J_entropy : Integrable (fun v => J v * |Real.log (J v)|) := by
  have hc : Continuous (fun v => |J v * Real.log (J v)|) :=
    (Real.continuous_mul_log.comp J_smooth.continuous).abs
  have hs : HasCompactSupport (fun v => |J v * Real.log (J v)|) := by
    apply J_compact.mono
    intro v hv
    by_contra hj
    have hz : J v = 0 := by simpa only [Function.mem_support, not_not] using hj
    simp only [Function.mem_support, hz, zero_mul, abs_zero, ne_eq, not_true_eq_false] at hv
  have hi : Integrable (fun v => |J v * Real.log (J v)|) :=
    hc.integrable_of_hasCompactSupport hs
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  rw [abs_mul, abs_of_nonneg (J_nonneg v)]

end BoltzmannNonuniqueness.JetThermalLaw

end

end

section

/-! # Absolute-entropy bounds under thermal scaling and translation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetThermalKernel
open BoltzmannNonuniqueness.JetThermalLaw

namespace BoltzmannNonuniqueness.JetThermalEntropy

theorem entropy_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ entropy x :=
  mul_nonneg hx (abs_nonneg _)

theorem entropy_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    entropy (x * y) ≤ y * entropy x + x * entropy y := by
  obtain rfl | hx := hx.eq_or_lt
  · simp [entropy]
  obtain rfl | hy := hy.eq_or_lt
  · simp [entropy]
  have h := mul_le_mul_of_nonneg_left (abs_add_le (Real.log x) (Real.log y))
    (mul_nonneg hx.le hy.le)
  rw [← Real.log_mul hx.ne' hy.ne'] at h
  unfold entropy
  nlinarith only [h]

theorem continuous_entropy_comp {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) : Continuous (fun x => entropy (f x)) := by
  have he : (fun x => entropy (f x)) = fun x => |f x * Real.log (f x)| := by
    funext x
    simp only [entropy, abs_mul, abs_of_nonneg (hpos x)]
  rw [he]
  exact (Real.continuous_mul_log.comp hf).abs

/-- Pointwise bound with a constant independent of the profile center. -/
theorem density_entropy_bound {d : ℝ} (hd : 0 < d) (a v : Velocity) :
    entropy (density d a v) ≤ (3 * |Real.log d|) * density d a v +
      scaled d a (fun w => entropy (J w)) v := by
  have he := entropy_mul_le (inv_nonneg.mpr (pow_nonneg hd.le 3)) (J_nonneg (d⁻¹ • (v - a)))
  have hlog : |Real.log ((d ^ 3)⁻¹)| = 3 * |Real.log d| := by
    rw [Real.log_inv, Real.log_pow, abs_neg, abs_mul]
    norm_num
  unfold density scaled
  unfold entropy at he
  rw [hlog] at he
  unfold entropy
  nlinarith only [he]

theorem entropyConstant_nonneg : 0 ≤ entropyConstant :=
  integral_nonneg (fun w => entropy_nonneg (J_nonneg w))

end BoltzmannNonuniqueness.JetThermalEntropy

end

end

section

/-! # The integrable hyperbolic axial weight of the cold datum -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetAxialWeight

theorem intervalIntegral_S (a b : ℝ) :
    (∫ x in a..b, S x) = Real.tanh b - Real.tanh a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => tanh_derivative x)
    (continuous_S.intervalIntegrable a b)

theorem intervalIntegral_S_le_two (a b : ℝ) : (∫ x in a..b, S x) ≤ 2 := by
  rw [intervalIntegral_S]
  linarith [Real.tanh_lt_one b, Real.neg_one_lt_tanh a]

theorem integrable_S : Integrable S := by
  apply integrable_of_intervalIntegral_norm_bounded (2 : ℝ)
    (a := fun r : ℝ => -r) (b := fun r : ℝ => r)
    (l := atTop)
    (fun r => (continuous_S.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    tendsto_neg_atTop_atBot tendsto_id
  apply Eventually.of_forall
  intro r
  have he : (fun x : ℝ => ‖S x‖) = S := by
    funext x
    exact Real.norm_of_nonneg (S_pos x).le
  rw [he]
  exact intervalIntegral_S_le_two _ _

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

section

/-! # Exponential control of the cold datum's axial entropy -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetAxialEntropy

theorem integrable_exp_neg_abs : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Iic 0) := by
    apply (integrableOn_exp_Iic 0).congr_fun _ measurableSet_Iic
    intro x hx
    dsimp only
    change x ≤ 0 at hx
    rw [abs_of_nonpos hx, neg_neg]
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Ioi 0) := by
    apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only
    rw [abs_of_pos hx]
  have h := hneg.union hpos
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem cosh_lower (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  linarith [Real.exp_pos (-|x|)]

theorem cosh_upper (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -|x| ≤ |x| by linarith [abs_nonneg x])
  linarith

theorem S_exp_bound (x : ℝ) : S x ≤ 4 * Real.exp (-2 * |x|) := by
  have hi := (inv_le_inv₀ (Real.cosh_pos x) (by positivity : 0 < Real.exp |x| / 2)).mpr
    (cosh_lower x)
  have he : (Real.exp |x| / 2)⁻¹ = 2 * Real.exp (-|x|) := by
    rw [inv_div, Real.exp_neg]
    ring
  rw [he] at hi
  have hs := (sq_le_sq₀ (inv_nonneg.mpr (Real.cosh_pos x).le) (by positivity)).mpr hi
  change S x ≤ (2 * Real.exp (-|x|)) ^ 2 at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num

theorem log_S_bound (x : ℝ) : |Real.log (S x)| ≤ 2 * |x| := by
  have hlog : 0 ≤ Real.log (Real.cosh x) := Real.log_nonneg (Real.one_le_cosh x)
  have hb : Real.log (Real.cosh x) ≤ |x| := by
    have h := Real.log_le_log (Real.cosh_pos x) (cosh_upper x)
    simpa only [Real.log_exp] using h
  simp only [S, Real.log_pow, Real.log_inv, abs_mul, abs_neg,
    abs_of_nonneg hlog]
  norm_num
  linarith

theorem entropy_exp_bound (x : ℝ) : S x * |Real.log (S x)| ≤ 8 * Real.exp (-|x|) := by
  have hb := mul_le_mul (S_exp_bound x) (log_S_bound x)
    (abs_nonneg _) (by positivity : 0 ≤ 4 * Real.exp (-2 * |x|))
  have he : |x| * Real.exp (-2 * |x|) ≤ Real.exp (-|x|) := by
    have hh : |x| ≤ Real.exp |x| :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp |x|)
    have h := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-2 * |x|)).le
    rw [← Real.exp_add] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  nlinarith

theorem integrable_axial_entropy : Integrable (fun x : ℝ => S x * |Real.log (S x)|) := by
  apply (integrable_exp_neg_abs.const_mul 8).mono'
  · exact (continuous_S.mul ((continuous_S.log (fun x => (S_pos x).ne')).abs)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg (S_pos x).le (abs_nonneg _))]
    exact entropy_exp_bound x

end BoltzmannNonuniqueness.JetAxialEntropy

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem scalarRelativeEntropy_le_power {m u p : ℝ} (hu : 0 ≤ u) (hp : 1 < p) :
    scalarRelativeEntropy m u ≤ u^p/(p-1)+|Real.log m| *u+m := by
  have hp' : 0 < p-1 := sub_pos.mpr hp
  have hpow : u*u^(p-1) = u^p := by
    by_cases hz : u = 0
    · simp [hz,Real.zero_rpow hp'.ne',Real.zero_rpow (by linarith : p ≠ 0)]
    · rw [mul_comm,← Real.rpow_add_one hz]
      congr 1
      ring
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hu hp') hu
  have he : u*(u^(p-1)/(p-1)) = u^p/(p-1) := by rw [← mul_div_assoc,hpow]
  rw [he] at hlog
  have hm := mul_le_mul_of_nonneg_right (neg_le_abs (Real.log m)) hu
  unfold scalarRelativeEntropy
  nlinarith

theorem abs_log_maxwellian_le (v : Velocity) :
    |Real.log (maxwellian v)| ≤ |-(3/2:ℝ)*Real.log (2*Real.pi)|+‖v‖^2/2 := by
  rw [log_maxwellian]
  exact (abs_sub (-(3/2:ℝ)*Real.log (2*Real.pi)) (‖v‖^2/2)).trans_eq
    (congrArg (fun x : ℝ => |-(3/2:ℝ)*Real.log (2*Real.pi)|+x)
      (abs_of_nonneg (show 0 ≤ ‖v‖^2/2 by positivity)))

theorem scalarRelativeEntropy_le_majorant {q B p u : ℝ} (hB : 0 ≤ B) (hp : 1 < p)
    (v : Velocity) (hu : 0 ≤ u) (hub : u ≤ B*H q v) :
    scalarRelativeEntropy (maxwellian v) u ≤ entropyPowerMajorant q B p v := by
  have hpow := Real.rpow_le_rpow hu hub (by linarith : 0 ≤ p)
  rw [Real.mul_rpow hB (H_nonneg q v)] at hpow
  have hquot := div_le_div_of_nonneg_right hpow (by linarith : 0 ≤ p-1)
  have hlog := mul_le_mul (abs_log_maxwellian_le v) hub hu (by positivity)
  have h := scalarRelativeEntropy_le_power (m := maxwellian v) hu hp
  unfold entropyPowerMajorant
  calc
    _ ≤ u^p/(p-1)+|Real.log (maxwellian v)| *u+maxwellian v := h
    _ ≤ (B^p*H q v^p)/(p-1)+
        (|-(3/2:ℝ)*Real.log (2*Real.pi)|+‖v‖^2/2)*(B*H q v)+maxwellian v := by
      linarith
    _ = _ := by ring

theorem entropyPowerMajorant_integrable {q B p : ℝ} (hq : q < 2)
    (hp : Integrable (fun v : Velocity => H q v^p)) :
    Integrable (entropyPowerMajorant q B p) := by
  have h := ((hp.const_mul (B^p/(p-1))).add
    (((integrable_H hq).const_mul (|-(3/2:ℝ)*Real.log (2*Real.pi)| *B)).add
      ((integrable_even_moment_H hq 1).const_mul (B/2)))).add integrable_maxwellian
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  simp only [entropyPowerMajorant,Nat.reduceMul,Pi.add_apply]
  ring

theorem bounded_relative_entropy_integrable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {q B p : ℝ} (hq : q < 2) (hB : 0 ≤ B)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hfb : ∀ z, f z ≤ B*H q z.2) :
    Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z)) (μ.prod volume) := by
  have hm : Measurable (fun z : X × Velocity => scalarRelativeEntropy (maxwellian z.2) (f z)) := by
    unfold scalarRelativeEntropy maxwellian
    fun_prop
  apply ((entropyPowerMajorant_integrable (B := B) hq hpi).comp_snd μ).mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos _) (hfn z))]
  exact scalarRelativeEntropy_le_majorant hB hp z.2 (hfn z) (hfb z)

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

section

/-! # Convex bounds for entropy under truncation and addition -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness

theorem scalarRelativeEntropy_convex (m : ℝ) :
    ConvexOn ℝ (Ici (0:ℝ)) (scalarRelativeEntropy m) := by
  refine ⟨convex_Ici _,?_⟩
  intro x hx y hy a b ha hb hab
  have h := Real.convexOn_mul_log.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold scalarRelativeEntropy
  calc
    _ = (a*x+b*y)*Real.log (a*x+b*y)-(a*x+b*y)*(1+Real.log m)+(a+b)*m := by rw [hab]; ring
    _ ≤ (a*(x*Real.log x)+b*(y*Real.log y))-(a*x+b*y)*(1+Real.log m)+(a+b)*m := by linarith
    _ = _ := by ring

theorem scalarRelativeEntropy_double (m x : ℝ) :
    scalarRelativeEntropy m (2*x) = 2*scalarRelativeEntropy m x+2*x*Real.log 2-m := by
  by_cases hx : x = 0
  · simp only [hx,scalarRelativeEntropy,mul_zero,zero_mul,sub_zero]
    ring
  · rw [scalarRelativeEntropy,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hx]
    unfold scalarRelativeEntropy
    ring

theorem scalarRelativeEntropy_add_le {m a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    scalarRelativeEntropy m (a+b) ≤ scalarRelativeEntropy m a+scalarRelativeEntropy m b+
      (a+b)*Real.log 2-m := by
  have h := (scalarRelativeEntropy_convex m).2 (show 2*a ∈ Ici (0:ℝ) by change 0 ≤ 2*a; positivity)
    (show 2*b ∈ Ici (0:ℝ) by change 0 ≤ 2*b; positivity)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ)+1/2 = 1)
  simp only [smul_eq_mul] at h
  rw [show (1/2:ℝ)*(2*a)+(1/2)*(2*b) = a+b by ring,
    scalarRelativeEntropy_double,scalarRelativeEntropy_double] at h
  linarith

theorem scalarRelativeEntropy_le_of_le {m u v : ℝ} (hm : 0 < m) (hu : 0 ≤ u) (huv : u ≤ v) :
    scalarRelativeEntropy m u ≤ scalarRelativeEntropy m v+m := by
  have hv : 0 ≤ scalarRelativeEntropy m v := by
    rw [scalarRelativeEntropy_eq hm]
    exact relativeEntropyDensity_nonneg (hu.trans huv) hm
  have h := (scalarRelativeEntropy_convex m).le_max_of_mem_Icc
    (show (0:ℝ) ∈ Ici (0:ℝ) by simp) (show v ∈ Ici (0:ℝ) by exact hu.trans huv) ⟨hu,huv⟩
  have hz : scalarRelativeEntropy m 0 = m := by simp [scalarRelativeEntropy]
  rw [hz] at h
  exact h.trans (max_le (by linarith) (by linarith [hm.le]))

end BoltzmannNonuniqueness

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

/-! # Absolute entropy of the cold datum's spatial factor -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetAxialWeight
open BoltzmannNonuniqueness.JetAxialEntropy
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetMaskMeasure

namespace BoltzmannNonuniqueness.JetSpatialEntropy

theorem scalar_scaled_integrable {f : ℝ → ℝ} (hf : Integrable f) {γ s : ℝ}
    (hγ : 0 < γ) (hs : 0 < s) : Integrable (fun z => f (γ * z / s)) := by
  have h := hf.comp_mul_left' (div_ne_zero hγ.ne' hs.ne')
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  congr 1
  ring

theorem scalar_scaled_integral (f : ℝ → ℝ) {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) :
    (∫ z, f (γ * z / s)) = (s / γ) * ∫ z, f z := by
  have he : (fun z => f (γ * z / s)) = fun z => f ((γ / s) * z) := by
    funext z
    congr 1
    ring
  rw [he, Measure.integral_comp_mul_left, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (div_pos hγ hs)), inv_div]

theorem massConstant_nonneg : 0 ≤ massConstant := integral_nonneg (fun z => (S_pos z).le)

theorem entropyConstant_nonneg : 0 ≤ entropyConstant :=
  integral_nonneg (fun z => entropy_nonneg (S_pos z).le)

theorem axial_entropy_bound {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (γ z : ℝ) :
    entropy (axialAmplitude K γ s z) ≤ axialMajorant K γ s z := by
  by_cases hz : z ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
  · rw [axialAmplitude, indicator_of_mem hz]
    exact entropy_mul_le (div_nonneg hK hs.le) (S_pos _).le
  · rw [axialAmplitude, indicator_of_notMem hz]
    simp only [entropy, zero_mul]
    exact add_nonneg (mul_nonneg (S_pos _).le (entropy_nonneg (div_nonneg hK hs.le)))
      (mul_nonneg (div_nonneg hK hs.le) (entropy_nonneg (S_pos _).le))

theorem axialMajorant_integrable {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (K : ℝ) :
    Integrable (axialMajorant K γ s) :=
  ((scalar_scaled_integrable integrable_S hγ hs).mul_const _).add
    ((scalar_scaled_integrable integrable_axial_entropy hγ hs).const_mul _)

theorem axial_entropy_integrable {K γ s : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) :
    Integrable (fun z => entropy (axialAmplitude K γ s z)) := by
  have he : (fun z => entropy (axialAmplitude K γ s z)) =
      (Ioo (-(1 / 8 : ℝ)) (1 / 8)).indicator (fun z => entropy ((K / s) * S (γ * z / s))) := by
    funext z
    by_cases hz : z ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simp only [axialAmplitude, indicator_of_mem hz]
    · simp only [axialAmplitude, indicator_of_notMem hz, entropy, zero_mul]
  apply (axialMajorant_integrable hγ hs K).mono'
  · rw [he]
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ measurableSet_Ioo
    exact (continuous_entropy_comp (continuous_const.mul (continuous_S.comp
      ((continuous_const.mul continuous_id).div_const s)))
        (fun z => mul_nonneg (div_nonneg hK hs.le) (S_pos _).le)).measurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (entropy_nonneg (axialAmplitude_nonneg hK hs.le γ z))]
    exact axial_entropy_bound hK hs γ z

theorem axial_entropy_integral {K γ s : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) :
    (∫ z, entropy (axialAmplitude K γ s z)) ≤
      (s / γ) * (entropy (K / s) * massConstant + (K / s) * entropyConstant) := by
  apply (integral_mono (axial_entropy_integrable hK hγ hs)
    (axialMajorant_integrable hγ hs K) (axial_entropy_bound hK hs γ)).trans_eq
  have hS : Integrable (fun z => S (γ * z / s)) := scalar_scaled_integrable integrable_S hγ hs
  have hE : Integrable (fun z => entropy (S (γ * z / s))) :=
    scalar_scaled_integrable integrable_axial_entropy hγ hs
  have hEI : (∫ z, entropy (S (γ * z / s))) =
      (s / γ) * ∫ z, entropy (S z) :=
    scalar_scaled_integral (fun z => entropy (S z)) hγ hs
  unfold axialMajorant
  rw [integral_add (hS.mul_const _) (hE.const_mul _),
    integral_mul_const, integral_const_mul, scalar_scaled_integral _ hγ hs, hEI]
  unfold massConstant entropyConstant
  ring

theorem spatial_entropy_eq (η K γ s : ℝ) (a : Bool) :
    (fun x : Space => entropy (spatial η K γ s a x)) =
      fun x => (mask η s a).indicator (fun _ => (1 : ℝ)) x.1 *
        entropy (axialAmplitude K γ s x.2) := by
  funext x
  by_cases hx : x.1 ∈ mask η s a <;> simp [spatial, hx, entropy]

theorem spatial_entropy_integrable {η K γ s : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    Integrable (fun x : Space => entropy (spatial η K γ s a x)) spaceVolume := by
  rw [spatial_entropy_eq]
  exact (indicator_integrable hη a).mul_prod (axial_entropy_integrable hK hγ hs)

theorem spatial_entropy_integral {η K γ s : ℝ} (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    (∫ x : Space, entropy (spatial η K γ s a x) ∂spaceVolume) ≤
      volume.real (mask η s a) * (s / γ) *
        (entropy (K / s) * massConstant + (K / s) * entropyConstant) := by
  rw [spatial_entropy_eq]
  dsimp only [spaceVolume]
  rw [integral_prod_mul ((mask η s a).indicator (fun _ => (1 : ℝ)))
    (fun z => entropy (axialAmplitude K γ s z)), integral_indicator (measurableSet_mask η s a),
    setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  have h := mul_le_mul_of_nonneg_left (axial_entropy_integral hK hγ hs)
    (measureReal_nonneg : 0 ≤ volume.real (mask η s a))
  simpa only [mul_assoc] using h

end BoltzmannNonuniqueness.JetSpatialEntropy

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

theorem center_norm (α γ s : ℝ) (a : Bool) (z : ℝ) :
    ‖center α γ s a z‖ = |AxialFlow.profile (sign a) α γ s z| := by
  have h := PlaneChart.norm_join_sq (0 : Transverse) (AxialFlow.profile (sign a) α γ s z)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  change ‖center α γ s a z‖ ^ 2 = _ at h
  nlinarith [sq_abs (AxialFlow.profile (sign a) α γ s z), norm_nonneg (center α γ s a z),
    abs_nonneg (AxialFlow.profile (sign a) α γ s z)]

theorem abs_sign (a : Bool) : |sign a| = 1 := by cases a <;> norm_num [sign]

theorem center_norm_bound {α : ℝ} (hα : 0 ≤ α) (γ s : ℝ) (a : Bool) (z : ℝ) :
    ‖center α γ s a z‖ ≤ 1 + α := by
  rw [center_norm]
  have h := AxialFlow.profile_sub_center_le (σ := sign a) (γ := γ) (s := s) (z := z) hα
  have ht := abs_add_le (AxialFlow.profile (sign a) α γ s z - sign a) (sign a)
  rw [sub_add_cancel, abs_sign] at ht
  linarith

theorem density_velocity_bound {d α : ℝ} (hd : 0 < d) (hα : 0 ≤ α)
    (η K γ s : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : JetPrototype.density η K α γ s d a p ≠ 0) : ‖p.2‖ < 1 + α + d := by
  have hthermal : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 :=
    right_ne_zero_of_mul hp
  exact (JetThermalLaw.density_velocity_bound hd hthermal).trans_le
    (add_le_add (center_norm_bound hα γ s a _) le_rfl)

theorem density_support_two {d α : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (η K γ s : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) : ‖p.2‖ < 2 := by
  have h := density_velocity_bound hd hα η K γ s a hp
  linarith

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integration of spatial weights against the cold thermal kernel -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalLaw

namespace BoltzmannNonuniqueness.JetWeightedKernel

theorem weighted_nonneg {d : ℝ} (hd : 0 ≤ d) (α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : ∀ x, 0 ≤ w x) {f : Velocity → ℝ} (hf : ∀ v, 0 ≤ f v)
    (p : JetPrototype.Phase) : 0 ≤ weighted d α γ s a w f p := by
  exact mul_nonneg (hw _) (mul_nonneg (inv_nonneg.mpr (pow_nonneg hd 3)) (hf _))

theorem weighted_measurable (d α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : Measurable w) {f : Velocity → ℝ} (hf : Measurable f) :
    Measurable (weighted d α γ s a w f) := by
  have hc : Measurable (fun p : JetPrototype.Phase => center α γ s a p.1.2) :=
    (measurable_center α γ s a).comp (measurable_snd.comp measurable_fst)
  have harg : Measurable (fun p : JetPrototype.Phase => d⁻¹ • (p.2 - center α γ s a p.1.2)) :=
    (measurable_const : Measurable (fun _ : JetPrototype.Phase => d⁻¹)).smul (measurable_snd.sub hc)
  exact (hw.comp measurable_fst).mul (measurable_const.mul (hf.comp harg))

theorem weighted_velocity_integral {d : ℝ} (hd : 0 < d) (α γ s : ℝ) (a : Bool)
    (w : Space → ℝ) (f : Velocity → ℝ) (x : Space) :
    (∫ v, weighted d α γ s a w f (x, v)) = w x * ∫ v, f v := by
  change (∫ v, w x * scaled d (center α γ s a x.2) f v) = _
  rw [integral_const_mul, integral_scaled f hd]

theorem weighted_integrable {d : ℝ} (hd : 0 < d) (α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : Measurable w) (hwi : Integrable w spaceVolume) (hwp : ∀ x, 0 ≤ w x)
    {f : Velocity → ℝ} (hf : Measurable f) (hfi : Integrable f) (hfp : ∀ v, 0 ≤ f v) :
    Integrable (weighted d α γ s a w f) (spaceVolume.prod volume) := by
  apply (integrable_prod_iff (weighted_measurable d α γ s a hw hf).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    exact (integrable_scaled hfi hd (center α γ s a x.2)).const_mul (w x)
  · have he : (fun x : Space => ∫ v, ‖weighted d α γ s a w f (x, v)‖) =
        fun x => w x * ∫ v, f v := by
      funext x
      simp_rw [Real.norm_of_nonneg (weighted_nonneg hd.le α γ s a hwp hfp _)]
      exact weighted_velocity_integral hd α γ s a w f x
    rw [he]
    exact hwi.mul_const _

theorem weighted_integral {d : ℝ} (hd : 0 < d) (α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : Measurable w) (hwi : Integrable w spaceVolume) (hwp : ∀ x, 0 ≤ w x)
    {f : Velocity → ℝ} (hf : Measurable f) (hfi : Integrable f) (hfp : ∀ v, 0 ≤ f v) :
    (∫ p, weighted d α γ s a w f p ∂spaceVolume.prod volume) =
      (∫ x, w x ∂spaceVolume) * ∫ v, f v := by
  rw [integral_prod _ (weighted_integrable hd α γ s a hw hwi hwp hf hfi hfp)]
  simp_rw [weighted_velocity_integral hd α γ s a]
  exact integral_mul_const _ _

end BoltzmannNonuniqueness.JetWeightedKernel

end

end

section

/-! # Absolute entropy of each actual cold-jet prototype -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalKernel
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetWeightedKernel

namespace BoltzmannNonuniqueness.JetPrototypeEntropy

theorem measurable_entropy {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) : Measurable (fun x => entropy (f x)) :=
  hf.mul (Real.measurable_log.comp hf).abs

theorem spatialWeight_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s)
    (η γ d : ℝ) (a : Bool) (x : Space) : 0 ≤ spatialWeight η K γ s d a x :=
  add_nonneg (entropy_nonneg (spatial_nonneg hK hs η γ a x))
    (mul_nonneg (by positivity) (spatial_nonneg hK hs η γ a x))

theorem spatialWeight_measurable (η K γ s d : ℝ) (a : Bool) :
    Measurable (spatialWeight η K γ s d a) :=
  (measurable_entropy (measurable_spatial η K γ s a)).add
    (measurable_const.mul (measurable_spatial η K γ s a))

theorem spatialWeight_integrable {η K γ s : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (d : ℝ) (a : Bool) :
    Integrable (spatialWeight η K γ s d a) spaceVolume :=
  (JetSpatialEntropy.spatial_entropy_integrable hη hK hγ hs a).add
    ((spatial_integrable hη K γ s a).const_mul _)

theorem entropy_le_majorant {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hd : 0 < d) (η α γ : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    entropy (density η K α γ s d a p) ≤ majorant η K α γ s d a p := by
  have hw := spatial_nonneg hK hs η γ a p.1
  have h₁ := entropy_mul_le hw
    (JetThermalLaw.density_nonneg hd.le (center α γ s a p.1.2) p.2)
  have h₂ := mul_le_mul_of_nonneg_left
    (density_entropy_bound hd (center α γ s a p.1.2) p.2) hw
  unfold density at *
  unfold JetThermalLaw.density at h₁ h₂
  unfold majorant weighted spatialWeight JetThermalLaw.density
  nlinarith only [h₁, h₂]

theorem majorant_integrable {η K γ s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    Integrable (majorant η K α γ s d a) (spaceVolume.prod volume) := by
  apply Integrable.add
  · exact weighted_integrable hd α γ s a (spatialWeight_measurable η K γ s d a)
      (spatialWeight_integrable hη hK hγ hs d a)
      (spatialWeight_nonneg hK hs.le η γ d a) J_smooth.continuous.measurable
      J_integrable J_nonneg
  · exact weighted_integrable hd α γ s a (measurable_spatial η K γ s a)
      (spatial_integrable hη K γ s a) (spatial_nonneg hK hs.le η γ a)
      (measurable_entropy J_smooth.continuous.measurable) JetThermalLaw.integrable_J_entropy
      (fun v => entropy_nonneg (J_nonneg v))

theorem density_entropy_integrable {η K γ s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    Integrable (fun p => entropy (density η K α γ s d a p))
      (spaceVolume.prod volume) := by
  apply (majorant_integrable hη hK hγ hs hd α a).mono'
  · exact (measurable_entropy (measurable_density η K α γ s d a)).aestronglyMeasurable
  · filter_upwards [] with p
    rw [Real.norm_of_nonneg (entropy_nonneg (density_nonneg hK hs.le hd.le η α γ a p))]
    exact entropy_le_majorant hK hs.le hd η α γ a p

theorem density_entropy_integral {η K γ s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    (∫ p, entropy (density η K α γ s d a p) ∂spaceVolume.prod volume) ≤
      (∫ x, entropy (spatial η K γ s a x) ∂spaceVolume) +
        (3 * |Real.log d| + JetThermalEntropy.entropyConstant) *
          ∫ x, spatial η K γ s a x ∂spaceVolume := by
  apply (integral_mono (density_entropy_integrable hη hK hγ hs hd α a)
    (majorant_integrable hη hK hγ hs hd α a)
    (entropy_le_majorant hK hs.le hd η α γ a)).trans_eq
  have hi₁ := weighted_integrable hd α γ s a (spatialWeight_measurable η K γ s d a)
    (spatialWeight_integrable hη hK hγ hs d a)
    (spatialWeight_nonneg hK hs.le η γ d a) J_smooth.continuous.measurable
    J_integrable J_nonneg
  have hi₂ := weighted_integrable hd α γ s a (measurable_spatial η K γ s a)
    (spatial_integrable hη K γ s a) (spatial_nonneg hK hs.le η γ a)
    (measurable_entropy J_smooth.continuous.measurable) JetThermalLaw.integrable_J_entropy
    (fun v => entropy_nonneg (J_nonneg v))
  unfold majorant
  rw [integral_add hi₁ hi₂,
    weighted_integral hd α γ s a (spatialWeight_measurable η K γ s d a)
      (spatialWeight_integrable hη hK hγ hs d a)
      (spatialWeight_nonneg hK hs.le η γ d a) J_smooth.continuous.measurable J_integrable J_nonneg,
    weighted_integral hd α γ s a (measurable_spatial η K γ s a)
      (spatial_integrable hη K γ s a) (spatial_nonneg hK hs.le η γ a)
      (measurable_entropy J_smooth.continuous.measurable) JetThermalLaw.integrable_J_entropy
      (fun v => entropy_nonneg (J_nonneg v)), J_integral, mul_one]
  unfold spatialWeight JetThermalEntropy.entropyConstant
  rw [integral_add (JetSpatialEntropy.spatial_entropy_integrable hη hK hγ hs a)
    ((spatial_integrable hη K γ s a).const_mul _), integral_const_mul]
  ring

end BoltzmannNonuniqueness.JetPrototypeEntropy

end

end

section

/-! # The scale-uniform, summable cold-jet entropy bound -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetMaskMeasure

namespace BoltzmannNonuniqueness.JetEntropyBound

theorem spatialConstant_nonneg {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 ≤ γ) :
    0 ≤ spatialConstant K γ := by
  have := JetSpatialEntropy.massConstant_nonneg
  have := JetSpatialEntropy.entropyConstant_nonneg
  unfold spatialConstant
  positivity

theorem constant_nonneg {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 ≤ γ) (d₀ : ℝ) :
    0 ≤ constant K γ d₀ := by
  have := spatialConstant_nonneg hK hγ
  have := JetThermalEntropy.entropyConstant_nonneg
  unfold constant
  positivity

theorem spatial_mass_bound {η K γ s : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    (∫ x, spatial η K γ s a x ∂spaceVolume) ≤ (8 * Real.pi * K / γ) * s ^ 2 := by
  have h := density_mass_bound hη hηmax hK hγ hs (show (0 : ℝ) < 1 by norm_num) 0 a
  rw [integral_prod _ (density_integrable hη hK hs.le (show (0 : ℝ) < 1 by norm_num) 0 γ a)] at h
  simpa only [density_velocity_integral (show (0 : ℝ) < 1 by norm_num)] using h

theorem spatial_entropy_bound {η K γ s : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    (∫ x, entropy (spatial η K γ s a x) ∂spaceVolume) ≤
      spatialConstant K γ * s ^ 2 * (1 + |Real.log s|) := by
  have hM := JetSpatialEntropy.massConstant_nonneg
  have hE := JetSpatialEntropy.entropyConstant_nonneg
  have hlog : |Real.log (K / s)| ≤ |Real.log K| + |Real.log s| := by
    rw [Real.log_div hK.ne' hs.ne']
    exact abs_sub _ _
  have heq : (s / γ) * (entropy (K / s) * JetSpatialEntropy.massConstant +
      (K / s) * JetSpatialEntropy.entropyConstant) =
      (K / γ) * (|Real.log (K / s)| * JetSpatialEntropy.massConstant +
        JetSpatialEntropy.entropyConstant) := by
    unfold entropy
    field_simp
  have hscalar : (|Real.log K| + |Real.log s|) * JetSpatialEntropy.massConstant +
      JetSpatialEntropy.entropyConstant ≤
      ((|Real.log K| + 1) * JetSpatialEntropy.massConstant + JetSpatialEntropy.entropyConstant) *
        (1 + |Real.log s|) := by
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (Real.log K)) hM) (abs_nonneg (Real.log s)),
      mul_nonneg hE (abs_nonneg (Real.log s))]
  calc
    _ ≤ volume.real (mask η s a) * ((s / γ) *
        (entropy (K / s) * JetSpatialEntropy.massConstant +
          (K / s) * JetSpatialEntropy.entropyConstant)) := by
      simpa only [mul_assoc] using JetSpatialEntropy.spatial_entropy_integral hK.le hγ hs a
    _ = volume.real (mask η s a) * (K / γ) *
        (|Real.log (K / s)| * JetSpatialEntropy.massConstant + JetSpatialEntropy.entropyConstant) := by
      rw [heq, mul_assoc]
    _ ≤ (4 * Real.pi * s ^ 2) * (K / γ) *
        ((|Real.log K| + |Real.log s|) * JetSpatialEntropy.massConstant +
          JetSpatialEntropy.entropyConstant) := by
      gcongr
      exact mask_area_uniform hη hηmax hs.le a
    _ ≤ (4 * Real.pi * s ^ 2) * (K / γ) *
        (((|Real.log K| + 1) * JetSpatialEntropy.massConstant +
          JetSpatialEntropy.entropyConstant) * (1 + |Real.log s|)) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by unfold spatialConstant; ring

theorem thermal_log_bound {d₀ s : ℝ} (hd₀ : 0 < d₀) (hs : 0 < s) :
    3 * |Real.log (d₀ * s ^ 10)| + JetThermalEntropy.entropyConstant ≤
      (3 * (|Real.log d₀| + 10) + JetThermalEntropy.entropyConstant) * (1 + |Real.log s|) := by
  have hlog : |Real.log (d₀ * s ^ 10)| ≤ |Real.log d₀| + 10 * |Real.log s| := by
    rw [Real.log_mul hd₀.ne' (pow_ne_zero _ hs.ne'), Real.log_pow]
    have h := abs_add_le (Real.log d₀) (10 * Real.log s)
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10), Nat.cast_ofNat] using h
  have hE := JetThermalEntropy.entropyConstant_nonneg
  nlinarith [mul_nonneg (abs_nonneg (Real.log d₀)) (abs_nonneg (Real.log s)),
    mul_nonneg hE (abs_nonneg (Real.log s))]

/-- The constant depends only on the fixed parameters, and is independent of the annular scale. -/
theorem prototype_entropy_bound {η K γ s d₀ : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hs : 0 < s) (hd₀ : 0 < d₀) (α : ℝ) (a : Bool) :
    (∫ p, entropy (density η K α γ s (d₀ * s ^ 10) a p) ∂spaceVolume.prod volume) ≤
      constant K γ d₀ * s ^ 2 * (1 + |Real.log s|) := by
  have hd : 0 < d₀ * s ^ 10 := mul_pos hd₀ (pow_pos hs _)
  have hsp := spatial_entropy_bound hη hηmax hK hγ hs a
  have hm := spatial_mass_bound hη hηmax hK.le hγ hs a
  have ht := thermal_log_bound hd₀ hs
  have hm0 : 0 ≤ ∫ x, spatial η K γ s a x ∂spaceVolume :=
    integral_nonneg (spatial_nonneg hK.le hs.le η γ a)
  calc
    _ ≤ (∫ x, entropy (spatial η K γ s a x) ∂spaceVolume) +
        (3 * |Real.log (d₀ * s ^ 10)| + JetThermalEntropy.entropyConstant) *
          ∫ x, spatial η K γ s a x ∂spaceVolume :=
      JetPrototypeEntropy.density_entropy_integral hη hK.le hγ hs hd α a
    _ ≤ spatialConstant K γ * s ^ 2 * (1 + |Real.log s|) +
        ((3 * (|Real.log d₀| + 10) + JetThermalEntropy.entropyConstant) * (1 + |Real.log s|)) *
          ((8 * Real.pi * K / γ) * s ^ 2) := by
      exact add_le_add hsp (mul_le_mul ht hm hm0 (by
        have := JetThermalEntropy.entropyConstant_nonneg
        positivity))
    _ = _ := by unfold constant; ring

end BoltzmannNonuniqueness.JetEntropyBound

end

end

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

theorem entropy_tsum {ι : Type*} {f : ι → ℝ}
    (hf : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) :
    entropy (∑' i, f i) = ∑' i, entropy (f i) := by
  classical
  by_cases h : ∃ i, f i ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hz : ∀ j, j ≠ i → f j = 0 := fun j hj => hf i j hj.symm hi
    rw [tsum_eq_single i hz, tsum_eq_single i]
    intro j hj
    simp [hz j hj, entropy]
  · have hz : ∀ i, f i = 0 := fun i => not_ne_iff.mp (not_exists.mp h i)
    simp [hz, entropy]

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

theorem term_entropy_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) (i : Index) :
    Integrable (fun p => entropy (term s₀ η K α γ d₀ i p)) (spaceVolume.prod volume) :=
  JetPrototypeEntropy.density_entropy_integrable hη hK hγ (DatumBounds.scale_pos hs₀ _)
    (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _)) α i.2

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

theorem entropy_datum {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    entropy (datum s₀ η K α γ d₀ p) = ∑' i, entropy (term s₀ η K α γ d₀ i p) :=
  JetSeries.entropy_tsum (term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p)

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

theorem entropy_summable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) :
    Summable (fun i : Index => ∫ p, entropy (term s₀ η K α γ d₀ i p) ∂spaceVolume.prod volume) := by
  have hs : Summable (fun j => JetEntropyBound.constant K γ d₀ *
      (jetScale s₀ η j ^ 2 * (1 + |Real.log (jetScale s₀ η j)|))) := by
    exact ((summable_nat_add_iff 1).mpr (DatumBounds.summable_entropyBound hs₀ hη)).mul_left _
  apply Summable.of_nonneg_of_le
    (fun i => integral_nonneg (fun p => entropy_nonneg (term_nonneg hs₀ hK.le hd₀.le η α γ i p)))
    (fun i => ?_) (summable_bool_extension (fun j => by
      have := JetEntropyBound.constant_nonneg hK.le hγ.le d₀
      positivity) hs)
  simpa only [mul_assoc, term, jetScale] using JetEntropyBound.prototype_entropy_bound hη.le hηmax hK hγ
    (DatumBounds.scale_pos hs₀ _) hd₀ α i.2

theorem datum_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) : Integrable (datum s₀ η K α γ d₀) (spaceVolume.prod volume) :=
  JetSeries.integrable_nonnegative_series (term_measurable s₀ η K α γ d₀)
    (term_integrable hs₀ hη.le hK hd₀ α γ) (term_nonneg hs₀ hK hd₀.le η α γ)
    (term_summable hs₀ hsmax hη hηmax K α γ d₀) (mass_summable hs₀ hη hηmax hK hγ hd₀ α)

theorem datum_entropy_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) :
    Integrable (fun p => entropy (datum s₀ η K α γ d₀ p)) (spaceVolume.prod volume) := by
  simp_rw [entropy_datum hs₀ hsmax hη hηmax]
  apply JetSeries.integrable_nonnegative_series
    (fun i => JetPrototypeEntropy.measurable_entropy (term_measurable s₀ η K α γ d₀ i))
    (term_entropy_integrable hs₀ hη.le hK.le hγ hd₀ α)
    (fun i p => entropy_nonneg (term_nonneg hs₀ hK.le hd₀.le η α γ i p))
    (fun p => JetSeries.summable_single_support ?_)
    (entropy_summable hs₀ hη hηmax hK hγ hd₀ α)
  intro i j hij hi
  have ht : term s₀ η K α γ d₀ i p ≠ 0 := by
    intro h
    exact hi (by simp [h, entropy])
  simp [term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p i j hij ht, entropy]

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

theorem thermal_width_le {s₀ η d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hd₀ : 0 ≤ d₀) (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (j : ℕ) :
    d₀ * jetScale s₀ η j ^ 10 ≤ 1 / 64 := by
  have hs : jetScale s₀ η j ≤ 1 / 8 := by
    change DatumBounds.scale s₀ η (j + 1) ≤ _
    calc
      _ ≤ DatumBounds.scale s₀ η 0 := scale_antitone hs₀.le hη (Nat.zero_le (j + 1))
      _ = s₀ := by simp [DatumBounds.scale]
      _ ≤ _ := hsmax
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (DatumBounds.scale_pos hs₀ _).le hs 10) hd₀).trans hwidth

theorem datum_support_two {s₀ η d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hd₀ : 0 < d₀) (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (K γ : ℝ) (p : JetPrototype.Phase)
    (hp : 2 ≤ ‖p.2‖) : datum s₀ η K α γ d₀ p = 0 := by
  have hz : ∀ i, term s₀ η K α γ d₀ i p = 0 := by
    intro i
    by_contra hi
    have hv := JetSupport.density_support_two
      (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _))
      (thermal_width_le hs₀ hsmax hη hd₀.le hwidth i.1) hα hαmax η K γ _ i.2 hi
    exact (not_lt_of_ge hp) hv
  simp only [datum, hz, tsum_zero]

theorem datum_energy_integrable {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    Integrable (fun p => datum s₀ η K α γ d₀ p * ‖p.2‖ ^ 2) (spaceVolume.prod volume) := by
  have hi := datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α
  apply (hi.mul_const 4).mono'
  · exact hi.aestronglyMeasurable.mul (continuous_snd.norm.pow 2).aestronglyMeasurable
  · filter_upwards [] with p
    have hn := datum_nonneg hs₀ hK hd₀.le η α γ p
    rw [Real.norm_of_nonneg (mul_nonneg hn (sq_nonneg _))]
    by_cases hv : 2 ≤ ‖p.2‖
    · rw [datum_support_two hs₀ hsmax hη.le hd₀ hwidth hα hαmax K γ p hv]
      simp
    · have hv' : ‖p.2‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg p.2]
      exact mul_le_mul_of_nonneg_left hv' hn

theorem datum_entropyMoment_integrable {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    Integrable (fun p => datum s₀ η K α γ d₀ p *
      (1 + ‖p.2‖ ^ 2 + |Real.log (datum s₀ η K α γ d₀ p)|)) (spaceVolume.prod volume) := by
  convert ((datum_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ α).add
    (datum_energy_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ hwidth hα hαmax)).add
    (datum_entropy_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [Pi.add_apply, entropy]
  ring

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

theorem eventually_truncated_eq {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    ∀ᶠ N in atTop, truncated s₀ η K α γ d₀ N p = datum s₀ η K α γ d₀ p := by
  by_cases h : ∃ i, term s₀ η K α γ d₀ i p ≠ 0
  · obtain ⟨i, hi⟩ := h
    apply eventually_atTop.mpr
    refine ⟨i.1 + 1, fun N hN => ?_⟩
    rw [truncated_at_nonzero hs₀ hsmax hη hηmax K α γ d₀ N p hi, ite_eq_left (by omega)]
  · have hz : ∀ i, term s₀ η K α γ d₀ i p = 0 := fun i => not_ne_iff.mp (not_exists.mp h i)
    apply Eventually.of_forall
    intro N
    simp only [truncated, datum, hz, ite_self, tsum_zero]

theorem truncated_tendsto {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    Tendsto (fun N => truncated s₀ η K α γ d₀ N p) atTop (𝓝 (datum s₀ η K α γ d₀ p)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_truncated_eq hs₀ hsmax hη hηmax K α γ d₀ p] with N hN
  exact hN.symm

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

theorem finiteEntropy {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    FiniteEntropyDatum (datum s₀ η K α γ d₀) := by
  refine ⟨Filter.Eventually.of_forall (fun p => ?_), ?_, ?_⟩
  · exact JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  · exact (integrable_pullback (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ α)).1
  · exact integrable_pullback
      (JetDatumMoments.datum_entropyMoment_integrable hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax)

end BoltzmannNonuniqueness.JetPeriodicDatum

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

/-! # Restricting a kinetic weak limit to any earlier time interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem timePositionVolume_restrict {t T : ℝ} (ht : t ≤ T) :
    (AnnularEnvelope.timePositionVolume T).restrict (Icc 0 t ×ˢ (univ : Set Position)) =
      AnnularEnvelope.timePositionVolume t := by
  rw [AnnularEnvelope.timePositionVolume,← Measure.prod_restrict,Measure.restrict_univ,
    Measure.restrict_restrict_of_subset (Icc_subset_Icc le_rfl ht)]
  rfl

theorem timePositionVolume_mono {t T : ℝ} (ht : t ≤ T) :
    AnnularEnvelope.timePositionVolume t ≤ AnnularEnvelope.timePositionVolume T := by
  rw [AnnularEnvelope.timePositionVolume,AnnularEnvelope.timePositionVolume]
  exact Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl ht) le_rfl) le_rfl

namespace Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.restrict_time {ν : Measure X} [SFinite ν] {t T : ℝ}
    {f : ℕ → (ℝ × Position) × X → ℝ} {g : (ℝ × Position) × X → ℝ}
    (h : WeakL1Converges ((AnnularEnvelope.timePositionVolume T).prod ν) f g) (ht : t ≤ T) :
    WeakL1Converges ((AnnularEnvelope.timePositionVolume t).prod ν) f g := by
  have hs := h.restrict_base (s := Icc 0 t ×ˢ (univ : Set Position)) (measurableSet_Icc.prod (MeasurableSet.univ : MeasurableSet (univ : Set Position)))
  rw [timePositionVolume_restrict ht] at hs
  exact hs

end Published
end BoltzmannNonuniqueness

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

theorem bounded_finiteEntropyDatum {q A p : ℝ} {f : Density}
    (hq : q < 2) (hA : 0 ≤ A) (hp : 1 < p)
    (hpi : Integrable (fun v : Velocity => H q v^p))
    (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ A*H q z.2) :
    FiniteEntropyDatum f := by
  have hfi : Integrable f := by
    apply (((integrable_H hq).const_mul A).comp_snd (volume : Measure Position)).mono'
      hfm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (hfn z)]
    exact hfb z
  have hEi : Integrable (fun z => ‖z.2‖^2*f z) := by
    have hmajor : Integrable (fun z : Phase => A*(‖z.2‖^2*H q z.2)) := by
      rw [Measure.volume_eq_prod]
      simpa only [Nat.reduceMul] using
        ((integrable_even_moment_H hq 1).const_mul A).comp_snd (volume : Measure Position)
    apply hmajor.mono' (((continuous_snd.norm.pow 2).measurable).mul hfm).aestronglyMeasurable
    filter_upwards [] with z
    simp only [Pi.mul_apply,Pi.pow_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hfn z))]
    exact (mul_le_mul_of_nonneg_left (hfb z) (sq_nonneg _)).trans_eq (by ring)
  have hHi : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z)) := by
    rw [Measure.volume_eq_prod]
    exact bounded_relative_entropy_integrable hq hA hp hpi hfm hfn hfb
  exact FiniteEntropyDatum.of_relativeEntropy_integrable (Filter.Eventually.of_forall hfn) hfi hEi hHi

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyUniformIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Entropy convergence of truncations with a vanishing bounded perturbation -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem scalarRelativeEntropy_truncation_perturbation_le {q C p a b f : ℝ}
    (hC : 0 ≤ C) (hp : 1 < p) (v : Velocity)
    (ha : 0 ≤ a) (haf : a ≤ f) (hb : 0 ≤ b) (hbg : b ≤ C*H q v) :
    scalarRelativeEntropy (maxwellian v) (a+b) ≤
      scalarRelativeEntropy (maxwellian v) f+entropyPowerMajorant q C p v+
        (f+C*H q v)*Real.log 2 := by
  have hs := scalarRelativeEntropy_add_le (m := maxwellian v) ha hb
  have hcut := scalarRelativeEntropy_le_of_le (maxwellian_pos v) ha haf
  have hhot := scalarRelativeEntropy_le_majorant hC hp v hb hbg
  have hmass := mul_le_mul_of_nonneg_right (add_le_add haf hbg)
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  linarith

theorem entropy_truncation_perturbation_tendsto {q C p : ℝ}
    (hq : q < 2) (hC : 0 ≤ C) (hp : 1 < p)
    (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : Density} (hf : FiniteEntropyDatum f)
    {a b : ℕ → Density} (ham : ∀ n, Measurable (a n)) (hbm : ∀ n, Measurable (b n))
    (ha : ∀ n z, 0 ≤ a n z ∧ a n z ≤ f z)
    (hb : ∀ n z, 0 ≤ b n z ∧ b n z ≤ C*H q z.2)
    (halim : ∀ z, Tendsto (fun n => a n z) atTop (𝓝 (f z)))
    (hblim : ∀ z, Tendsto (fun n => b n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, scalarRelativeEntropy (maxwellian z.2) (a n z+b n z))
      atTop (𝓝 (relativeEntropy f)) := by
  let B : Phase → ℝ := fun z => scalarRelativeEntropy (maxwellian z.2) (f z)+
    entropyPowerMajorant q C p z.2+(f z+C*H q z.2)*Real.log 2
  have hHi : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z)) := by
    apply (FiniteEntropyDatum.integrable_relativeEntropy hf).congr
    filter_upwards [] with z
    exact (scalarRelativeEntropy_eq (maxwellian_pos z.2) (f z)).symm
  have hBi : Integrable B := by
    exact (hHi.add ((entropyPowerMajorant_integrable (B := C) hq hpi).comp_snd volume)).add
      (((FiniteEntropyDatum.integrable hf).add (((integrable_H hq).const_mul C).comp_snd volume)).mul_const _)
  have hlim := tendsto_integral_of_dominated_convergence B (fun n => by
    have hm : Measurable (fun z : Phase => scalarRelativeEntropy (maxwellian z.2) (a n z+b n z)) := by
      have hsum := (ham n).add (hbm n)
      have hM : Measurable (fun z : Phase => maxwellian z.2) := by unfold maxwellian; fun_prop
      exact ((hsum.mul hsum.log).sub (hsum.mul (measurable_const.add hM.log))).add hM
    exact hm.aestronglyMeasurable) hBi (fun n => by
      filter_upwards [] with z
      rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos z.2)
        (add_nonneg (ha n z).1 (hb n z).1))]
      exact scalarRelativeEntropy_truncation_perturbation_le hC hp z.2 (ha n z).1 (ha n z).2
        (hb n z).1 (hb n z).2) (by
      filter_upwards [] with z
      have hs : Tendsto (fun n => a n z+b n z) atTop (𝓝 (f z)) := by
        simpa only [add_zero] using (halim z).add (hblim z)
      exact ((scalarRelativeEntropy_continuous (maxwellian z.2)).tendsto (f z)).comp hs)
  have he : (∫ z, scalarRelativeEntropy (maxwellian z.2) (f z)) = relativeEntropy f := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact scalarRelativeEntropy_eq (maxwellian_pos z.2) (f z)
  rwa [he] at hlim

end BoltzmannNonuniqueness

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

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem entropy_dissipation_of_liminfs {H D : ℕ → ℝ≥0∞} {C : ℕ → ℝ}
    {h d : ℝ≥0∞} {c : ℝ}
    (hh : h ≤ liminf H atTop) (hd : d ≤ liminf D atTop)
    (hC : Tendsto C atTop (𝓝 c))
    (hupper : ∀ᶠ n in atTop, H n+D n ≤ ENNReal.ofReal (C n)) :
    h+d ≤ ENNReal.ofReal c := by
  have hm := liminf_le_liminf hupper
  rw [(ENNReal.tendsto_ofReal hC).liminf_eq] at hm
  exact (add_le_add hh hd).trans ((ennreal_liminf_add_nat H D).trans hm)

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

theorem color_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) :
    0 ≤ color s₀ η K α γ d₀ q N i p := by
  unfold color
  split_ifs
  · exact div_nonneg (JetDatum.term_nonneg hs₀ hK hd₀ η α γ _ _) (H_nonneg _ _)
  · exact le_rfl

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

theorem color_summable {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    Summable (fun i => color s₀ η K α γ d₀ q N i p) :=
  JetSeries.summable_single_support (color_disjoint hs₀ hsmax hη hηmax K α γ d₀ q N p)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Finite weighted bounds for the countably labeled periodic seed -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem finite_sum_le_seed {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (α γ q : ℝ) (N : ℕ) (u : Finset JetLattice.Label) (p : JetPrototype.Phase) :
    ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤ seed s₀ η K α γ d₀ q N p :=
  (color_summable hs₀ hsmax hη hηmax K α γ d₀ q N p).sum_le_tsum u
    (fun i _ => color_nonneg hs₀ hK hd₀ η α γ q N i p)

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

section

/-! # The actual labeled periodic approximation on a common local interval -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem initial_color_bounds {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (α γ q : ℝ) (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p) :
    (∀ i p, 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ initial s₀ η K α γ d₀ q N h₀ p) ∧
    (∀ u : Finset JetLattice.Label, ∀ p,
      ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤ initial s₀ η K α γ d₀ q N h₀ p) := by
  have hf (u : Finset JetLattice.Label) (p) : ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤
      initial s₀ η K α γ d₀ q N h₀ p :=
    (finite_sum_le_seed hs₀ hsmax hη hηmax hK hd₀ α γ q N u p).trans (le_add_of_nonneg_right (hh₀ p))
  refine ⟨?_,hf⟩
  intro i p
  classical
  exact ⟨color_nonneg hs₀ hK hd₀ η α γ q N i p,by simpa using hf {i} p⟩

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapDilationScales
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Relative entropy convergence of the actual cap-shooting initial data -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem periodicInitial_entropy_tendsto {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (hq : 1 < q) (hqmax : q < 2)
    {ell : ℕ → ℝ} (hell : ∀ n, ell n ∈ Set.Icc (0:ℝ) 2) :
    Tendsto (fun n => relativeEntropy (periodicInitial s₀ η K α γ d₀ q n (ell n)))
      atTop (𝓝 (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀))) := by
  let δ : ℕ → ℝ := fun n => DatumBounds.scale s₀ η (n+1)
  let C : ℝ := 2*(HotSeedProfile.bound/HotSeedProfile.normLower q)
  have hC : 0 ≤ C := mul_nonneg (by norm_num)
    (div_nonneg HotSeedProfile.bound_pos.le (HotSeedProfile.normLower_pos q).le)
  have hδ (n : ℕ) : 0 < δ n := DatumBounds.scale_pos hs₀ _
  have hδmax (n : ℕ) : δ n ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    exact h.trans (by linarith)
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    (DatumBounds.scale_tendsto_zero s₀ hη).comp (tendsto_add_atTop_nat 1)
  let a : ℕ → Density := fun n => JetPeriodicDatum.truncated s₀ η K α γ d₀ n
  let b : ℕ → Density := fun n z => ell n*HotSeedProfile.periodicDensity q (δ n) z
  have ha : ∀ n z, 0 ≤ a n z ∧ a n z ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ z := by
    intro n z
    have hn := JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ
      (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z))
    rcases JetTruncation.truncated_eq_or_zero hs₀ hsmax hη hηmax K α γ d₀ n
      (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) with he | he
    · change 0 ≤ JetTruncation.truncated s₀ η K α γ d₀ n
        (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) ∧
        JetTruncation.truncated s₀ η K α γ d₀ n
          (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) ≤
        JetDatum.datum s₀ η K α γ d₀ (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z))
      rw [he]
      exact ⟨hn,le_rfl⟩
    · change 0 ≤ JetTruncation.truncated s₀ η K α γ d₀ n
        (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) ∧
        JetTruncation.truncated s₀ η K α γ d₀ n
          (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)) ≤
        JetDatum.datum s₀ η K α γ d₀ (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z))
      rw [he]
      exact ⟨le_rfl,hn⟩
  have hb (n : ℕ) (z : Phase) : 0 ≤ b n z ∧ b n z ≤ C*δ n*H q z.2 := by
    refine ⟨mul_nonneg (hell n).1 (HotSeedProfile.periodicDensity_nonneg (hδ n) (hδmax n) z),?_⟩
    have h := mul_le_mul (hell n).2 (HotSeedProfile.periodicDensity_bound (by linarith : 0 ≤ q)
      (hδ n) (hδmax n) z) (HotSeedProfile.periodicDensity_nonneg (hδ n) (hδmax n) z) (by norm_num : (0:ℝ) ≤ 2)
    exact h.trans_eq (by dsimp [C] <;> ring)
  obtain ⟨p,hp,hpi⟩ := exists_integrable_rpow_H hq hqmax
  have hlim := entropy_truncation_perturbation_tendsto hqmax hC hp hpi
    (JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax)
    (a := a) (b := b)
    (fun n => JetPeriodicDatum.measurable_pullback (JetTruncation.truncated_measurable s₀ η K α γ d₀ n))
    (fun n => (HotSeedProfile.periodicDensity_measurable q (δ n)).const_mul (ell n)) ha
    (fun n z => ⟨(hb n z).1, (hb n z).2.trans (by
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC (hδmax n)) (H_nonneg q z.2))⟩)
    (fun z => JetTruncation.truncated_tendsto hs₀ hsmax hη hηmax K α γ d₀
      (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative z)))
    (fun z => by
      apply squeeze_zero (fun n => (hb n z).1) (fun n => (hb n z).2)
      simpa only [mul_zero,zero_mul] using (hδlim.const_mul C).mul_const (H q z.2))
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  unfold relativeEntropy
  apply integral_congr_ae
  filter_upwards [] with z
  rw [periodicInitial_eq hs₀ hsmax hη hηmax]
  exact (scalarRelativeEntropy_eq (maxwellian_pos z.2) (a n z+b n z)).symm

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakEntropyMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem positiveEvolution_nonnegative (t : ℝ) (p : Phase) : 0 ≤ positiveEvolution T f₀ g t p :=
  le_max_right _ _

end BoltzmannNonuniqueness.MildCollisionSolution

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionConservation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The moving cutoff preserves entropy dissipation at the actual weak collision limit -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem cutoffExtendedProduction_eq_rates (b : ℝ) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    cutoffExtendedProduction b f z =
      extendedEntropyProduction (truncatedPostRate b f z) (truncatedPreRate b f z) := by
  by_cases hz : ‖z.1.2.1-z.1.2.2‖ < b
  · simp only [cutoffExtendedProduction,truncatedPostRate,truncatedPreRate,
      Set.indicator_apply,Set.mem_ofPred_eq,hz,↓reduceIte,postRate_formula,preRate]
    simpa only [mul_assoc] using (extendedEntropyProduction_scale
      (collisionKernel_nonneg z.1.2.1 z.1.2.2 z.2)
      (mul_nonneg (hf _) (hf _)) (mul_nonneg (hf _) (hf _))).symm
  · simp [cutoffExtendedProduction,truncatedPostRate,truncatedPreRate,hz,extendedEntropyProduction]

theorem rateDissipation_le_liminf_cutoff {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfn : ∀ n p, 0 ≤ f n p)
    (hgm : Measurable g) (hgn : ∀ p, 0 ≤ g p)
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hfi : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity))))
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) :
    rateDissipation μ g ≤ liminf (fun n => cutoffExtendedDissipation μ (b n) (f n)) atTop := by
  have hr : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => ‖z.1.2.1-z.1.2.2‖) := by
    fun_prop
  have hs n : MeasurableSet {z : (X × (Velocity × Velocity)) × Sphere | ‖z.1.2.1-z.1.2.2‖ < b n} :=
    measurableSet_lt hr measurable_const
  have hpre := (weak_preRate h hfi).moving_cutoff
    (fun n => preRate_integrable (hfm n) (hfn n) (hfi n))
    (fun n z => preRate_nonneg (hfn n) z) hr hb
  have hpost := (weak_postRate hfm hgm h hfi).moving_cutoff
    (fun n => postRate_integrable (hfm n) (hfn n) (hfi n))
    (fun n z => preRate_nonneg (hfn n) (scatterTriple z)) hr hb
  have hi := Published.weak_production_liminf hpost hpre
    (fun n => (postRate_integrable (hfm n) (hfn n) (hfi n)).indicator (hs n))
    (fun n => (preRate_integrable (hfm n) (hfn n) (hfi n)).indicator (hs n))
    (ae_of_all _ (fun z => preRate_nonneg hgn (scatterTriple z)))
    (ae_of_all _ (fun z => preRate_nonneg hgn z))
  have hm := ENNReal.le_liminf_mul (u := fun _ : ℕ => (4:ℝ≥0∞)⁻¹)
    (v := fun n => ∫⁻ z, extendedEntropyProduction
      (truncatedPostRate (b n) (f n) z) (truncatedPreRate (b n) (f n) z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) (f := atTop)
  have hle := (mul_le_mul_right hi (4:ℝ≥0∞)⁻¹).trans (by
    simpa only [liminf_const,Pi.mul_def,truncatedPostRate,truncatedPreRate] using hm)
  simpa only [rateDissipation,cutoffExtendedDissipation,cutoffExtendedProduction_eq_rates _ (hfn _),truncatedPostRate,truncatedPreRate] using hle

end BoltzmannNonuniqueness.CollisionCompactness

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

/-! # The actual finite periodic approximations satisfy entropy with dissipation -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem entropy_dissipation_inequality (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 < T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hf₀ : Measurable f₀) (hf₀b : ∀ z, 0 ≤ f₀ z ∧ f₀ z ≤ R) :
    ENNReal.ofReal (relativeEntropy (F.torusEvolution T))+
      CollisionCompactness.cutoffExtendedDissipation (AnnularEnvelope.timePositionVolume T) b
        (kineticDensity F.torusEvolution) ≤
      ENNReal.ofReal (relativeEntropy (TorusFlight.initialDensity q f₀)) := by
  let E : Evolution := F.torusEvolution
  let a : Density := TorusFlight.initialDensity q f₀
  let r := TorusFlight.along (cutoffPhysicalSource b E)
  have hEm : Measurable (fun z : ℝ × Phase => E z.1 z.2) :=
    (JetCopyDatum.torusPhysical_measurable F.measurable_value q).comp MeasurableEquiv.prodAssoc.symm.measurable
  have hEn : ∀ t z, 0 ≤ E t z := fun t z =>
    JetCopyDatum.torusPhysical_nonneg (fun u => (F.value_bounds u).1) q _
  have hEb : ∀ t z, E t z ≤ R*H q z.2 := by
    intro t z
    have h := mul_le_mul_of_nonneg_left (F.value_bounds
      (t,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1),z.2))).2 (H_nonneg q z.2)
    exact h.trans_eq (mul_comm _ _)
  have ham : Measurable a := TorusFlight.initialDensity_measurable hf₀ q
  have han : ∀ z, 0 ≤ a z := fun z => mul_nonneg (H_nonneg q z.2) (hf₀b _).1
  have hab : ∀ z, a z ≤ R*H q z.2 := by
    intro z
    exact (mul_le_mul_of_nonneg_left (hf₀b _).2 (H_nonneg q z.2)).trans_eq (mul_comm _ _)
  have hcT : (fun z => E T (TorusFlight.flight T z)) =ᵐ[volume] entropyPath a r T :=
    TorusFlight.characteristic hcarleman F hq₁ hq₂ hb hR hT.le hTU hloss hf₀
  have hc : (fun z : ℝ × Phase => E z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume] (fun z => entropyPath a r z.1 z.2) := by
    have h := TorusFlight.spacetime_mild hcarleman F hq₁ hq₂ hb hR hT.le hTU hloss hf₀
    have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [h,ht] with z hz hzt
    rw [Published.timePrimitive_eq_interval hzt] at hz
    exact hz
  exact bounded_mild_entropy_dissipation_limit_q80 hcarleman hq₁ hq₂ hb hR hT
    hEm hEn hEb ham han hab hc hcT

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_SubcapCapLocalAdmissibility
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite entropy-dissipation bounds for approximations below the cap -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem Approximation.entropy_dissipation
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ENNReal.ofReal (relativeEntropy (F.solution.torusEvolution t))+
      CollisionCompactness.cutoffExtendedDissipation (AnnularEnvelope.timePositionVolume t) (N+1)
        (torusPhysical q F.solution.value) ≤
      ENNReal.ofReal (relativeEntropy (periodicInitial s₀ η K α γ d₀ q N F.coefficient)) := by
  have hδ : 0 < DatumBounds.scale s₀ η (N+1) := DatumBounds.scale_pos hs₀ _
  have hδmax : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh : ∀ p, 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds hδ hδmax q
    intro p
    exact mul_nonneg F.coefficient_mem.1 (hb p).1
  have hn (p) : 0 ≤ initial s₀ η K α γ d₀ q N
      (fun p => F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p := by
    simpa using (initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh).2 ∅ p
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have h := F.solution.entropy_dissipation_inequality hcarleman hq₁ hq₂ (by positivity)
    (show 0 ≤ 2*F.amplitude from mul_nonneg (by norm_num) F.amplitude_pos.le) ht htT le_rfl hm
    (fun p => ⟨hn p,F.initial_bound p⟩)
  have he : TorusFlight.initialDensity q (initial s₀ η K α γ d₀ q N
      (fun p => F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)) =
      periodicInitial s₀ η K α γ d₀ q N F.coefficient := by
    funext p
    exact mul_comm _ _
  rw [he] at h
  exact h

theorem Approximation.finiteEntropy
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : Approximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2) (t : ℝ) :
    FiniteEntropyDatum (F.solution.torusEvolution t) := by
  obtain ⟨p,hp,hpi⟩ := exists_integrable_rpow_H hq₁ hq₂
  apply bounded_finiteEntropyDatum (A := 2*F.amplitude) hq₂ (mul_nonneg (by norm_num) F.amplitude_pos.le) hp hpi
  · exact (torusPhysical_measurable F.solution.measurable_value q).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  · exact fun z => torusPhysical_nonneg (fun u => (F.solution.value_bounds u).1) q _
  · intro z
    exact (mul_le_mul_of_nonneg_left (F.solution.value_bounds
      (t,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1),z.2))).2
      (H_nonneg q z.2)).trans_eq (mul_comm _ _)

theorem Approximation.entropy_dissipation_extended
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2) (F.solution.torusEvolution t z)))+
      CollisionCompactness.cutoffExtendedDissipation (AnnularEnvelope.timePositionVolume t) (N+1)
        (torusPhysical q F.solution.value) ≤
      ENNReal.ofReal (relativeEntropy (periodicInitial s₀ η K α γ d₀ q N F.coefficient)) := by
  have hi := F.finiteEntropy hq₁ hq₂ t
  have hsi : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (F.solution.torusEvolution t z)) :=
    (FiniteEntropyDatum.integrable_relativeEntropy hi).congr (ae_of_all _ (fun z =>
      (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
  have hn : ∀ z, 0 ≤ F.solution.torusEvolution t z := fun z =>
    torusPhysical_nonneg (fun u => (F.solution.value_bounds u).1) q _
  have he : relativeEntropy (F.solution.torusEvolution t) =
      ∫ z, scalarRelativeEntropy (maxwellian z.2) (F.solution.torusEvolution t z) :=
    integral_congr_ae (ae_of_all _ (fun z => (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
  have h := F.entropy_dissipation hcarleman hs₀ hsmax hη hηmax hK hd₀ hq₁ hq₂ ht htT
  rw [he,ofReal_integral_eq_lintegral_ofReal hsi (ae_of_all _ (fun z =>
    scalarRelativeEntropy_nonneg (maxwellian_pos z.2) (hn z)))] at h
  exact h


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Every-time entropy and dissipation bounds for limits below the cap -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem TightFamily.entropy_mild_limit_of_convergence_q80_oai
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ} (hφ : StrictMono φ)
    (S : MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g)
    (hpair : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => CollisionCompactness.pairDensity
        (torusPhysical q (F.approximation (φ n)).solution.value)) (CollisionCompactness.pairDensity g))
    (htrace : ∀ t ∈ Icc 0 F.time, Published.WeakL1Converges volume
      (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
      (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t)) :
    ∀ t ∈ Ioc 0 F.time,
        (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2)
          (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t z)))+
        CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) g ≤
          ENNReal.ofReal (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀)) := by
  intro t ht
  let f : ℕ → (ℝ × Position) × Velocity → ℝ :=
    fun n => torusPhysical q (F.approximation (φ n)).solution.value
  have hfm n : Measurable (f n) :=
    torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hfn n p : 0 ≤ f n p := torusPhysical_nonneg
    (fun u => ((F.approximation (φ n)).solution.value_bounds u).1) q p
  have hfi n := FiniteEntropyDatum.integrable ((F.approximation (φ n)).finiteEntropy hq₁ hq₂ t)
  have hH := (htrace t ⟨ht.1.le,ht.2⟩).entropy_liminf hfi
    (fun n => ae_of_all _ (fun z => hfn n ((t,z.1),z.2)))
    (ae_of_all _ (fun z => MildCollisionSolution.positiveEvolution_nonnegative t z))
    (by unfold maxwellian; fun_prop) integrable_maxwellian_phase
    (ae_of_all _ (fun z => maxwellian_pos z.2))
  have hpairt := hpair.restrict_time ht.2
  have hpint n : Integrable (CollisionCompactness.pairDensity (f n))
      ((AnnularEnvelope.timePositionVolume t).prod volume) :=
    (memLp_one_iff_integrable.mp (F.pairs_ui.memLp (φ n))).mono_measure
      (Measure.prod_mono (timePositionVolume_mono ht.2) le_rfl)
  have hb : Tendsto (fun n => (φ n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n, (φ n:ℝ) ≤ (φ n:ℝ)+1)
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hD := CollisionCompactness.rateDissipation_le_liminf_cutoff hfm hfn S.measurable
    S.nonnegative hpairt hpint hb
  have hC := (periodicInitial_entropy_tendsto hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax hq₁ hq₂
    (fun n => (F.approximation n).coefficient_mem)).comp hφ.tendsto_atTop
  exact entropy_dissipation_of_liminfs hH hD hC (Eventually.of_forall (fun n =>
    (F.approximation (φ n)).entropy_dissipation_extended hcarleman hs₀ hsmax hη hηmax
      hK.le hd₀.le hq₁ hq₂ ht.1 ht.2))


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.entropy_mild_limit_of_convergence_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.entropy_mild_limit_of_convergence_q80_oai
