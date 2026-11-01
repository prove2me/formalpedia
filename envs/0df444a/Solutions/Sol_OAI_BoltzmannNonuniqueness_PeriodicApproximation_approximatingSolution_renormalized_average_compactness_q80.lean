-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:26:30.375926+00:00
-- url     : https://prove2.me/submissions/b7c495ee-2b48-449c-a1d0-6e12d4779535

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_approximatingSolution_renormalizedLocalizedSource_uniformIntegrable_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_Published_glps1988Proposition3_q80

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

protected theorem comp {ι' : Type*} (g : ι' → ι) (hf : UnifIntegrable f p μ) :
    UnifIntegrable (f ∘ g) p μ :=
  ⟨fun _ hε => (hf.1 hε).imp fun _ ⟨hδ, h⟩ => ⟨hδ, fun i s => h (g i) s⟩, fun i => hf.2 (g i)⟩

end UnifIntegrable

/-! ### `UniformIntegrable` -/


/-! ### `UnifTight` -/

end OAI

end UnifIntegrableCompat
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Removing a finite prefix without changing the common sequence index -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

theorem zeroPrefix_eventually {X : Type*} (N : ℕ) (f : ℕ → X → ℝ) :
    ∀ᶠ n in atTop, zeroPrefix N f n = f n := by
  filter_upwards [eventually_ge_atTop N] with n hn
  exact ite_eq_left hn

theorem uniformIntegrable_zeroPrefix {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℝ} {N : ℕ} {p : ℝ≥0∞}
    (h : UniformIntegrable (fun n => f (n+N)) p μ) :
    UniformIntegrable (zeroPrefix N f) p μ := by
  constructor
  · apply OAI.UnifIntegrable.of_enn
    intro ε hε
    obtain ⟨δ,hδ,hs⟩ := OAI.UnifIntegrable.enn_spec h.1 ε hε
    refine ⟨δ,hδ,fun n s hμs => ?_⟩
    by_cases hn : N ≤ n
    · simpa only [zeroPrefix,ite_eq_left hn,Nat.sub_add_cancel hn] using hs (n-N) s hμs
    · simp only [zeroPrefix,ite_eq_right hn,eLpNorm_zero]
      exact bot_le
    intro n
    by_cases hn : N ≤ n
    · simpa only [zeroPrefix,ite_eq_left hn,Nat.sub_add_cancel hn] using h.aestronglyMeasurable (n-N)
    · simp only [zeroPrefix,ite_eq_right hn]
      exact aestronglyMeasurable_zero
  · obtain ⟨C,hC⟩ := h.2
    refine ⟨C,fun n => ?_⟩
    by_cases hn : N ≤ n
    · simpa only [zeroPrefix,ite_eq_left hn,Nat.sub_add_cancel hn] using hC (n-N)
    · simp only [zeroPrefix,ite_eq_right hn,eLpNorm_zero]
      exact bot_le

end BoltzmannNonuniqueness.Compactness

end

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

section

/-! # A common GLPS subsequence when each source has its own finite prefix -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

theorem GLPS1988Proposition3.countable_tail_sources_tests (hGLPS : GLPS1988Proposition3)
    (r : ℕ → ℕ → KineticPhase → ℝ) (R : ℕ → ℝ) (hR : ∀ j, 0 < R j)
    (hsupp : ∀ j n, ∀ᵐ z ∂(volume : Measure KineticPhase), R j < ‖z.2‖ → r j n z = 0)
    (hUI : ∀ j, ∃ N : ℕ, UniformIntegrable (fun n => r j (n+N)) 1 volume)
    (ψ : ℕ → Velocity → ℝ)
    (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocalL1Converges (fun n => resolventAverage (r j (φ n)) (ψ j)) (g j) := by
  choose N hN using hUI
  let r' := fun j => Compactness.zeroPrefix (N j) (r j)
  have hui j : UniformIntegrable (r' j) 1 volume :=
    Compactness.uniformIntegrable_zeroPrefix (hN j)
  have hs j n : ∀ᵐ z ∂(volume : Measure KineticPhase), R j < ‖z.2‖ → r' j n z = 0 := by
    by_cases hn : N j ≤ n
    · simpa only [r',Compactness.zeroPrefix,ite_eq_left hn] using hsupp j n
    · exact ae_of_all _ (by simp [r',Compactness.zeroPrefix,hn])
  obtain ⟨φ,g,hφ,hg⟩ := hGLPS.countable_sources_tests r' R hR hs hui ψ hψ hψc
  refine ⟨φ,g,hφ,fun j => ⟨(hg j).1,fun K hK => ?_⟩⟩
  apply ((hg j).2 K hK).congr'
  filter_upwards [hφ.tendsto_atTop.eventually (Compactness.zeroPrefix_eventually (N j) (r j))]
    with n hn
  dsimp only [r']
  rw [hn]

end BoltzmannNonuniqueness.Published

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

end BoltzmannNonuniqueness.Renormalization

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_RenormalizedIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

/-! # Renormalization of a nonnegative integral path -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Renormalization

theorem integral_path_data {a b A : ℝ} {r : ℝ → ℝ} (hab : a ≤ b)
    (hr : IntervalIntegrable r volume a b) :
    AbsolutelyContinuousOnInterval (fun t => A+∫ s in a..t, r s) a b ∧
      (∀ᵐ t, t ∈ Icc a b → HasDerivAt (fun t => A+∫ s in a..t, r s) (r t) t) := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => A) a b := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  refine ⟨hc.add (hr.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc),?_⟩
  filter_upwards [hr.ae_hasDerivAt_integral] with t ht hmem
  exact (ht (by simpa only [uIcc_of_le hab] using hmem) a left_mem_uIcc).const_add A

theorem weighted_tested_integral_path (β : Renormalization)
    {a b m A : ℝ} {r ψ ψ' : ℝ → ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hr : IntervalIntegrable r volume a b)
    (hn : ∀ t ∈ Icc a b, 0 ≤ A+∫ s in a..t, r s)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hψ' : ∀ᵐ t, t ∈ Icc a b → HasDerivAt ψ (ψ' t) t) :
    (∫ t in a..b, derivWithin β.toFun (Ici 0) ((A+∫ s in a..t, r s)/m)*r t*ψ t+
      m*β.toFun ((A+∫ s in a..t, r s)/m)*ψ' t) =
      m*β.toFun ((A+∫ s in a..b, r s)/m)*ψ b-m*β.toFun (A/m)*ψ a := by
  obtain ⟨hp,hd⟩ := integral_path_data hab hr (A := A)
  simpa only [intervalIntegral.integral_same,add_zero] using
    β.weighted_tested_chain_rule hab hm hp hn hd hψ hψ'

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Exponential localization of a renormalized integral characteristic -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Renormalization

theorem localized_integral_path (β : Renormalization) {t m A : ℝ} {r χ : ℝ → ℝ}
    (ht : 0 ≤ t) (hm : 0 < m) (hr : IntervalIntegrable r volume 0 t)
    (hn : ∀ s ∈ Icc 0 t, 0 ≤ A+∫ u in 0..s, r u) (hχ : ContDiff ℝ 1 χ) :
    χ t*(m*β.toFun ((A+∫ s in 0..t, r s)/m)) =
      Real.exp (-t)*χ 0*(m*β.toFun (A/m))+
      ∫ s in 0..t, Real.exp (-(t-s))*(χ s*(derivWithin β.toFun (Ici 0)
        ((A+∫ u in 0..s, r u)/m)*r s)+
        (deriv χ s+χ s)*(m*β.toFun ((A+∫ u in 0..s, r u)/m))) := by
  let ψ : ℝ → ℝ := fun s => Real.exp (s-t)*χ s
  let ψ' : ℝ → ℝ := fun s => Real.exp (s-t)*(deriv χ s+χ s)
  have hp : ContDiff ℝ 1 ψ := by
    apply ContDiff.mul _ hχ
    exact Real.contDiff_exp.comp (contDiff_id.sub contDiff_const)
  have hd : ∀ s, HasDerivAt ψ (ψ' s) s := by
    intro s
    have he : HasDerivAt (fun u : ℝ => Real.exp (u-t)) (Real.exp (s-t)) s := by
      simpa only [id_eq,mul_one] using ((hasDerivAt_id s).sub_const t).exp
    convert he.mul (hχ.differentiable (by norm_num) s).hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [ψ,ψ']
    ring
  have h := β.weighted_tested_integral_path ht hm hr hn
    hp.contDiffOn.absolutelyContinuousOnInterval
    (ae_of_all _ (fun s _ => hd s))
  have hleft : (∫ s in 0..t, derivWithin β.toFun (Ici 0)
      ((A+∫ u in 0..s, r u)/m)*r s*ψ s+
      m*β.toFun ((A+∫ u in 0..s, r u)/m)*ψ' s) =
    ∫ s in 0..t, Real.exp (-(t-s))*(χ s*(derivWithin β.toFun (Ici 0)
      ((A+∫ u in 0..s, r u)/m)*r s)+
      (deriv χ s+χ s)*(m*β.toFun ((A+∫ u in 0..s, r u)/m))) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [ψ,ψ']
    rw [show s-t = -(t-s) by ring]
    ring
  rw [hleft] at h
  dsimp only [ψ] at h
  simp only [sub_self,Real.exp_zero,one_mul,zero_sub] at h
  linarith

end BoltzmannNonuniqueness.Renormalization

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

theorem transportDerivative_eq_zero {χ : KineticPhase → ℝ} {z : KineticPhase}
    (hz : z ∉ tsupport χ) : transportDerivative χ z = 0 := by
  unfold transportDerivative
  rw [fderiv_of_notMem_tsupport ℝ hz]
  rfl

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

end BoltzmannNonuniqueness.TransportCutoff

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicInitialEntropyLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_EuclideanKineticMap
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

/-! # Localized renormalized characteristics in Euclidean coordinates -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem projected_characteristic (p : Velocity × Velocity) (t : ℝ) :
    projectedPhase ((characteristic p t).1.2,(characteristic p t).2) =
      TorusFlight.flight t (projectedPhase p) := by
  apply Prod.ext
  · funext i
    change ((p.1 i+t*p.2 i : ℝ) : AddCircle (1:ℝ)) =
      (p.1 i : AddCircle (1:ℝ))+(t*p.2 i : ℝ)
    rw [AddCircle.coe_add]
  · rfl

theorem BoundedCutoffSolution.renormalized_localized_path (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (β : Renormalization)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (p : Phase) :
    χ t*S.renormalizedDensity β (t,TorusFlight.flight t p) =
      Real.exp (-t)*χ 0*(maxwellian p.2*β.toFun (f₀ p/maxwellian p.2))+
      ∫ r in 0..t, Real.exp (-(t-r))*(χ r*S.renormalizedSource β (r,TorusFlight.flight r p)+
        (deriv χ r+χ r)*S.renormalizedDensity β (r,TorusFlight.flight r p)) := by
  have he (r : ℝ) (hr : r ∈ Icc 0 t) :
      f₀ p+(∫ s in 0..r, S.source (s,TorusFlight.flight s p)-
        lossBound N*S.density (s,TorusFlight.flight s p)) = S.density (r,TorusFlight.flight r p) :=
    (S.characteristic_integral hN ⟨hr.1,hr.2.trans ht.2⟩ p).symm
  have h := β.localized_integral_path ht.1 (maxwellian_pos p.2)
    (S.collision_path_integrable hN p t)
    (fun r hr => (he r hr).symm ▸ S.nonnegative (r,TorusFlight.flight r p)) hχ
  rw [he t ⟨ht.1,le_rfl⟩] at h
  change _ = _+_ at h ⊢
  calc
    _ = _ := h
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht.1] at hr
      dsimp only [renormalizedSource,renormalizedDensity,collision]
      rw [he r hr]
      rfl

theorem BoundedCutoffSolution.euclidean_renormalized_localized
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T)
    (β : Renormalization) {χ : Published.KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hzero : ∀ p, χ (characteristic p 0) = 0)
    (p : Velocity × Velocity) :
    χ (characteristic p t)*S.euclideanRenormalizedDensity β (characteristic p t) =
      ∫ r in 0..t, Real.exp (-(t-r))*(χ (characteristic p r)*
        S.euclideanRenormalizedSource β (characteristic p r)+
        (transportDerivative χ (characteristic p r)+χ (characteristic p r))*
          S.euclideanRenormalizedDensity β (characteristic p r)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (characteristic p) := by unfold characteristic; fun_prop
  have H := S.renormalized_localized_path hN ht β ((hχ.comp hc).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (projectedPhase p)
  have hder (r : ℝ) : deriv (fun r => χ (characteristic p r)) r =
      transportDerivative χ (characteristic p r) :=
    (TransportCutoff.hasDerivAt_along (hχ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p r).deriv
  dsimp only [Function.comp_def] at H
  rw [hzero,mul_zero,zero_mul,zero_add] at H
  have hd (r : ℝ) : S.euclideanRenormalizedDensity β (characteristic p r) =
      S.renormalizedDensity β (r,TorusFlight.flight r (projectedPhase p)) := by
    unfold euclideanRenormalizedDensity
    rw [projected_characteristic]
    rfl
  have hs (r : ℝ) : S.euclideanRenormalizedSource β (characteristic p r) =
      S.renormalizedSource β (r,TorusFlight.flight r (projectedPhase p)) := by
    unfold euclideanRenormalizedSource
    rw [projected_characteristic]
    rfl
  simpa only [hd,hs,hder] using H

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual renormalized approximants are localized transport resolvents -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T U : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.renormalized_resolvent (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hUT : U ≤ T) (β : Renormalization) {χ : Published.KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hzero : ∀ p, χ (characteristic p 0) = 0)
    (z : Published.KineticPhase) (ht : z.1.1 ∈ Icc 0 U) :
    χ z*S.euclideanRenormalizedDensity β z = Published.transportResolvent
      (localizedSource U χ (S.euclideanRenormalizedDensity β) (S.euclideanRenormalizedSource β)) z := by
  have h := S.euclidean_renormalized_localized hN ⟨ht.1,ht.2.trans hUT⟩ β hχ hzero
    (EuclideanFlight.flight (-z.1.1) (z.1.2,z.2))
  rw [EuclideanFlight.characteristic_endpoint] at h
  rw [TransportPrimitive.transportResolvent_eq
    (fun w hw => localizedSource_causal U χ _ _ w hw) z ht.1]
  rw [h]
  apply intervalIntegral.integral_congr
  intro t ht'
  rw [uIcc_of_le ht.1] at ht'
  dsimp only
  rw [EuclideanFlight.characteristic_back,localizedSource_on χ _ _ _ ⟨ht'.1,ht'.2.trans ht.2⟩]

theorem BoundedCutoffSolution.renormalized_average_resolvent
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) (hUT : U ≤ T) (β : Renormalization)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p, χ (characteristic p 0) = 0) (ψ : Velocity → ℝ)
    (z : Published.SpaceTime) (ht : z.1 ∈ Icc 0 U) :
    (∫ v, ψ v*(χ (z,v)*S.euclideanRenormalizedDensity β (z,v))) =
      Published.resolventAverage (localizedSource U χ (S.euclideanRenormalizedDensity β)
        (S.euclideanRenormalizedSource β)) ψ z := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => congrArg (fun a => ψ v*a)
    (S.renormalized_resolvent hN hUT β hχ hzero (z,v) ht))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual renormalized velocity averages have one common local subsequence -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_renormalized_average_compactness_q80_oai
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (T R : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (hR : ∀ j, 0 < R j)
    (β : ℕ → Renormalization) (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hχc : ∀ j, HasCompactSupport (χ j))
    (hχx : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hχv : ∀ j, tsupport (χ j) ⊆ {z | ‖z.2‖ ≤ R j})
    (hχzero : ∀ j p, χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocallyIntegrable (g j) volume ∧ ∀ K : Set Published.SpaceTime, IsCompact K →
        K ⊆ {z | z.1 ∈ Icc 0 (T j)} →
        Tendsto (fun n => eLpNorm (fun z =>
          (∫ v, ψ j v*(χ j (z,v)*
            (approximatingSolution f hfm (φ n)).euclideanRenormalizedDensity (β j) (z,v)))-g j z)
          1 (volume.restrict K)) atTop (𝓝 0) := by
  let r : ℕ → ℕ → Published.KineticPhase → ℝ := fun j n => TransportCutoff.localizedSource (T j) (χ j)
    ((approximatingSolution f hfm n).euclideanRenormalizedDensity (β j))
    ((approximatingSolution f hfm n).euclideanRenormalizedSource (β j))
  have hs j n : ∀ᵐ z ∂(volume : Measure Published.KineticPhase), R j < ‖z.2‖ → r j n z = 0 :=
    ae_of_all _ (fun z hz => TransportCutoff.localizedSource_velocity_support (hχv j) _ _ z hz)
  have hui j : ∃ N : ℕ, UniformIntegrable (fun n => r j (n+N)) 1 volume :=
    ⟨Nat.ceil (T j),approximatingSolution_renormalizedLocalizedSource_uniformIntegrable_q80
      f hfm hf hi (hT j) (β j) (hχ j) (hχc j) (hχx j)⟩
  obtain ⟨φ,g,hφ,hg⟩ := Published.glps1988Proposition3_q80.countable_tail_sources_tests
    r R hR hs hui ψ hψ hψc
  refine ⟨φ,g,hφ,fun j => ⟨(hg j).1,fun K hK hKT => ?_⟩⟩
  apply ((hg j).2 K hK).congr'
  filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop (Nat.ceil (T j)))] with n hn
  have hbound : T j ≤ (φ n:ℝ)+1 := by
    have hc := Nat.le_ceil (T j)
    have hn' : (Nat.ceil (T j):ℝ) ≤ (φ n:ℝ) := by exact_mod_cast hn
    linarith
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  have he := (approximatingSolution f hfm (φ n)).renormalized_average_resolvent
    (by positivity) hbound (β j) (hχ j) (hχzero j) (ψ j) z (hKT hz)
  exact congrArg (fun a => a-g j z) he.symm

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness_q80_oai := @OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness_q80_oai
