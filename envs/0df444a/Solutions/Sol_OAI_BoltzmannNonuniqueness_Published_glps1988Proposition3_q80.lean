-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.Published.glps1988Proposition3_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:28:04.183575+00:00
-- url     : https://prove2.me/submissions/5c71869f-f971-4042-b880-f5f72dbf863f

import Mathlib
import Definitions.Def_OAIQ080A002

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

theorem spec (hp : p ≠ 0) (hp' : p ≠ ∞) (hfu : UniformIntegrable f p μ) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε := by
  rcases eq_top_or_lt_top ε with rfl | hεt
  · exact ⟨0, fun _ => le_top⟩
  obtain ⟨C, hC⟩ := hfu.toMathlib.spec hp hp' (ENNReal.toReal_pos hε.ne' hεt.ne)
  exact ⟨C, fun i => (hC i).trans (ENNReal.ofReal_toReal hεt.ne).le⟩

end UniformIntegrable


/-! ### `UnifTight` -/

end OAI

end UnifIntegrableCompat
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityFourierMultiplier
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Nonconcentration of Lebesgue velocities on affine transport hyperplanes -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem inner_velocity_surjective {ξ : Velocity} (hξ : ξ ≠ 0) :
    Function.Surjective (innerSL ℝ ξ : Velocity →ₗ[ℝ] ℝ) := by
  intro y
  refine ⟨(y / inner ℝ ξ ξ) • ξ, ?_⟩
  have hn : inner ℝ ξ ξ ≠ 0 := (real_inner_self_pos.mpr hξ).ne'
  change inner ℝ ξ ((y / inner ℝ ξ ξ) • ξ) = y
  rw [real_inner_smul_right]
  exact div_mul_cancel₀ y hn

theorem affine_velocity_hyperplane_null (τ : ℝ) {ξ : Velocity} (hξ : ξ ≠ 0) :
    (volume : Measure Velocity) {v | τ + inner ℝ ξ v = 0} = 0 := by
  have ha : ∀ᵐ y : ℝ ∂volume, y ∈ ({-τ} : Set ℝ)ᶜ := by
    simpa only [mem_compl_iff,mem_singleton_iff] using volume.ae_ne (-τ)
  have h := (ae_comp_linearMap_mem_iff (innerSL ℝ ξ : Velocity →ₗ[ℝ] ℝ)
    (volume : Measure Velocity) (volume : Measure ℝ) (inner_velocity_surjective hξ)
    (measurableSet_singleton (-τ)).compl).mpr ha
  have hz : ∀ᵐ v : Velocity ∂volume, ¬(τ + inner ℝ ξ v = 0) := by
    filter_upwards [h] with v hv he
    apply hv
    change inner ℝ ξ v = -τ
    linarith
  simpa only [not_not] using ae_iff.mp hz

theorem evolution_velocity_hyperplane_null {τ : ℝ} {ξ : Velocity}
    (h : (τ,ξ) ≠ 0) : (volume : Measure Velocity) {v | τ + inner ℝ ξ v = 0} = 0 := by
  by_cases hξ : ξ = 0
  · have hτ : τ ≠ 0 := by
      intro he
      apply h
      simp [he,hξ]
    simp [hξ,hτ]
  · exact affine_velocity_hyperplane_null τ hξ

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Decay and continuity of the localized transport multiplier -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem velocityMultiplier_nonneg (n : ℕ) (k : SpaceTime) (v : Velocity) :
    0 ≤ velocityMultiplier n k v := by unfold velocityMultiplier; positivity

theorem velocityMultiplier_le_one (n : ℕ) (k : SpaceTime) (v : Velocity) :
    velocityMultiplier n k v ≤ 1 := by
  unfold velocityMultiplier
  exact (inv_le_one₀ (by positivity)).mpr (by nlinarith [sq_nonneg ((n:ℝ)*(k.1+inner ℝ k.2 v))])

theorem velocityMultiplier_continuous (n : ℕ) :
    Continuous (fun p : SpaceTime × Velocity => velocityMultiplier n p.1 p.2) := by
  unfold velocityMultiplier
  apply Continuous.inv₀
  · fun_prop
  · intro p
    positivity

theorem velocityMultiplier_antitone (k : SpaceTime) (v : Velocity) :
    Antitone (fun n => velocityMultiplier n k v) := by
  intro n m hnm
  unfold velocityMultiplier
  apply inv_anti₀ (by positivity)
  have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
  rw [mul_pow,mul_pow]
  exact add_le_add_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg n) hcast 2) (sq_nonneg _)) _

theorem velocityMultiplier_tendsto {k : SpaceTime} {v : Velocity}
    (h : k.1+inner ℝ k.2 v ≠ 0) :
    Tendsto (fun n => velocityMultiplier n k v) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => (n : ℝ)^2*(k.1+inner ℝ k.2 v)^2) atTop atTop :=
    hn.atTop_mul_const (sq_pos_of_ne_zero h)
  have hh : Tendsto (fun n : ℕ => 1+(n : ℝ)^2*(k.1+inner ℝ k.2 v)^2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 hs
  simpa only [velocityMultiplier,mul_pow,Function.comp_def] using tendsto_inv_atTop_zero.comp hh

theorem velocityMultiplier_integrable (R : ℝ) (n : ℕ) (k : SpaceTime) :
    IntegrableOn (velocityMultiplier n k) (Metric.closedBall (0 : Velocity) R) := by
  exact ((velocityMultiplier_continuous n).comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
    (isCompact_closedBall _ _)

theorem velocityMultiplierMass_nonneg (R : ℝ) (n : ℕ) (k : SpaceTime) :
    0 ≤ velocityMultiplierMass R n k :=
  integral_nonneg (velocityMultiplier_nonneg n k)

theorem velocityMultiplierMass_antitone (R : ℝ) (k : SpaceTime) :
    Antitone (fun n => velocityMultiplierMass R n k) := by
  intro n m hnm
  exact integral_mono (velocityMultiplier_integrable R m k)
    (velocityMultiplier_integrable R n k) (fun v => velocityMultiplier_antitone k v hnm)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform decay of the transport multiplier on the unit frequency sphere -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem velocityMultiplierMass_continuous (R : ℝ) (n : ℕ) :
    Continuous (velocityMultiplierMass R n) := by
  have : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  apply continuous_of_dominated (bound := fun _ : Velocity => (1 : ℝ))
  · intro k
    exact ((velocityMultiplier_continuous n).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro k
    exact ae_of_all _ (fun v => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (velocityMultiplier_nonneg n k v)] using
        velocityMultiplier_le_one n k v)
  · exact integrable_const 1
  · exact ae_of_all _ (fun v => (velocityMultiplier_continuous n).comp
      (continuous_id.prodMk continuous_const))

theorem velocityMultiplierMass_tendsto (R : ℝ) {k : SpaceTime} (hk : k ≠ 0) :
    Tendsto (fun n => velocityMultiplierMass R n k) atTop (𝓝 0) := by
  have : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  have hz : ∀ᵐ v : Velocity ∂volume, k.1+inner ℝ k.2 v ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using evolution_velocity_hyperplane_null hk
  have hlim : ∀ᵐ v ∂volume.restrict (Metric.closedBall (0 : Velocity) R),
      Tendsto (fun n => velocityMultiplier n k v) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae hz] with v hv
    exact velocityMultiplier_tendsto hv
  have h := tendsto_integral_of_dominated_convergence (fun _ : Velocity => (1 : ℝ))
    (fun n => (velocityMultiplier_integrable R n k).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => ae_of_all _ (fun v => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (velocityMultiplier_nonneg n k v)] using
        velocityMultiplier_le_one n k v)) hlim
  simpa only [integral_zero,velocityMultiplierMass] using h

theorem velocityMultiplierMass_uniform_decay (R : ℝ) :
    TendstoUniformlyOn (velocityMultiplierMass R) (fun _ => 0) atTop
      (Metric.sphere (0 : SpaceTime) 1) := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto (isCompact_sphere _ _)
  · intro n
    exact (velocityMultiplierMass_continuous R n).continuousOn
  · intro k _
    exact velocityMultiplierMass_antitone R k
  · exact continuousOn_const
  · intro k hk
    apply velocityMultiplierMass_tendsto R
    intro he
    have hn : ‖k‖ = 1 := mem_sphere_zero_iff_norm.mp hk
    rw [he,norm_zero] at hn
    norm_num at hn

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The localized multiplier mass is uniformly small outside a frequency ball -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem velocityMultiplier_smul (a : ℝ) (n : ℕ) (k : SpaceTime) (v : Velocity) :
    velocityMultiplier n (a • k) v = (1+((n:ℝ)*a*(k.1+inner ℝ k.2 v))^2)⁻¹ := by
  simp only [velocityMultiplier,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,real_inner_smul_left]
  congr 2
  ring

theorem velocityMultiplier_large_scale {a : ℝ} {n : ℕ} (ha : (n:ℝ) ≤ a)
    (k : SpaceTime) (v : Velocity) :
    velocityMultiplier 1 (a • k) v ≤ velocityMultiplier n k v := by
  rw [velocityMultiplier_smul,velocityMultiplier]
  simp only [Nat.cast_one,one_mul]
  apply inv_anti₀ (by positivity)
  rw [mul_pow,mul_pow]
  exact add_le_add_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg n) ha 2) (sq_nonneg _)) _

theorem velocityMultiplierMass_large_scale (R : ℝ) {a : ℝ} {n : ℕ} (ha : (n:ℝ) ≤ a)
    (k : SpaceTime) : velocityMultiplierMass R 1 (a • k) ≤ velocityMultiplierMass R n k :=
  integral_mono (velocityMultiplier_integrable R 1 (a • k))
    (velocityMultiplier_integrable R n k) (velocityMultiplier_large_scale ha k)

theorem velocityMultiplierMass_high_frequency (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : SpaceTime, (N:ℝ) ≤ ‖k‖ → velocityMultiplierMass R 1 k < ε := by
  have hu := (Metric.tendstoUniformlyOn_iff.mp (velocityMultiplierMass_uniform_decay R)) ε hε
  rcases Filter.eventually_atTop.mp hu with ⟨n,hn⟩
  refine ⟨max n 1,by omega,?_⟩
  intro k hk
  have hkpos : 0 < ‖k‖ := lt_of_lt_of_le (by exact_mod_cast (show 0 < max n 1 by omega)) hk
  let e : SpaceTime := ‖k‖⁻¹ • k
  have he : e ∈ Metric.sphere (0 : SpaceTime) 1 := by
    rw [mem_sphere_zero_iff_norm]
    dsimp [e]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hkpos.ne']
  have heq : ‖k‖ • e = k := by
    dsimp [e]
    rw [smul_smul,mul_inv_cancel₀ hkpos.ne',one_smul]
  have hb := velocityMultiplierMass_large_scale R hk e
  rw [heq] at hb
  have hs := hn (max n 1) (le_max_left _ _) e he
  have hs' : velocityMultiplierMass R (max n 1) e < ε := by
    simpa only [Real.dist_eq,zero_sub,abs_neg,
      abs_of_nonneg (velocityMultiplierMass_nonneg R (max n 1) e)] using hs
  exact hb.trans_lt hs'

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The complex resolvent multiplier and its exact squared norm -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem complexVelocityMultiplier_norm_sq (n : ℕ) (k : SpaceTime) (v : Velocity) :
    ‖complexVelocityMultiplier n k v‖^2 = velocityMultiplier n k v := by
  rw [complexVelocityMultiplier,norm_inv,inv_pow,Complex.sq_norm]
  simp [Complex.normSq_apply,velocityMultiplier]
  ring

theorem complexVelocityMultiplier_norm_le_one (n : ℕ) (k : SpaceTime) (v : Velocity) :
    ‖complexVelocityMultiplier n k v‖ ≤ 1 := by
  have h := velocityMultiplier_le_one n k v
  rw [← complexVelocityMultiplier_norm_sq] at h
  nlinarith [norm_nonneg (complexVelocityMultiplier n k v)]

theorem complexVelocityMultiplier_continuous (n : ℕ) :
    Continuous (fun p : SpaceTime × Velocity => complexVelocityMultiplier n p.1 p.2) := by
  unfold complexVelocityMultiplier
  apply Continuous.inv₀
  · fun_prop
  · intro p h
    have hr := congrArg Complex.re h
    norm_num at hr

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_L2PairingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Squared integral pairings for the velocity multiplier estimate -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem L2_norm_sq_integral (a : Lp ℂ 2 μ) :
    ‖a‖^2 = ∫ x, ‖a x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def]
  rw [← integral_re (L2.integrable_inner a a)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [inner_self_eq_norm_sq_to_K,RCLike.re_ofReal_pow])

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SpacetimeFourierCoordinates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Hilbert coordinates for the evolution transport Fourier transform -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem spacetimeHilbert_measurePreserving :
    MeasurePreserving spacetimeHilbertEquiv (volume : Measure SpaceTime) volume :=
  WithLp.volume_preserving_toLp ℝ Velocity

theorem characteristicFrequency (k : FourierSpace) (v : Velocity) :
    inner ℝ k (characteristicDirection v) = (WithLp.ofLp k).1 + inner ℝ (WithLp.ofLp k).2 v := by
  simp [characteristicDirection,WithLp.prod_inner_apply,RCLike.inner_apply]

theorem spacetimeHilbert_translation (z : SpaceTime) (s : ℝ) (v : Velocity) :
    spacetimeHilbertEquiv (z.1-s,z.2-s • v) =
      spacetimeHilbertEquiv z - s • characteristicDirection v := by
  apply WithLp.ofLp_injective
  change (z.1-s,z.2-s • v) = (z.1-s*1,z.2-s • v)
  simp only [mul_one]

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_FourierL2Identification
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # The L2 Fourier transform and the classical integral have the same smooth pairings -/
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace BoltzmannNonuniqueness.Published

theorem fourier_L2_schwartz_pairing {f : FourierSpace → ℂ} (hf : MemLp f 2 volume)
    (g : 𝓢(FourierSpace, ℂ)) :
    (∫ x, g x * (𝓕 (hf.toLp f) : Lp ℂ 2 volume) x) = ∫ x, (𝓕 g) x * f x := by
  let a : Lp ℂ 2 volume := hf.toLp f
  have h := congrArg (fun T : 𝓢'(FourierSpace, ℂ) => T g)
    (Lp.fourier_toTemperedDistribution_eq a)
  simp only [TemperedDistribution.fourier_apply,Lp.toTemperedDistribution_apply] at h
  calc
    _ = ∫ x, (𝓕 g) x * a x := h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]

theorem fourier_integral_schwartz_pairing {f : FourierSpace → ℂ} (hf : Integrable f)
    (g : 𝓢(FourierSpace, ℂ)) :
    (∫ x, g x * 𝓕 f x) = ∫ x, (𝓕 g) x * f x := by
  have he : (innerₗ FourierSpace).flip = innerₗ FourierSpace := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact real_inner_comm x y
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure FourierSpace))
    (ν := (volume : Measure FourierSpace)) (L := innerₗ FourierSpace)
    Real.continuous_fourierChar continuous_inner g.integrable hf
  rw [he] at h
  exact h.symm

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Classical and Hilbert-space Fourier transforms agree on L1 intersect L2 -/
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap Topology
namespace BoltzmannNonuniqueness.Published

theorem fourier_L2_ae_eq_integral {f : FourierSpace → ℂ}
    (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    (fun x => (𝓕 (h₂.toLp f) : Lp ℂ 2 volume) x) =ᵐ[volume] 𝓕 f := by
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (h₂.toLp f))).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
  let ψ : 𝓢(FourierSpace, ℂ) := hs'.toSchwartzMap hg'
  have h := (fourier_L2_schwartz_pairing h₂ ψ).trans
    (fourier_integral_schwartz_pairing hf ψ).symm
  change (∫ x, (g x : ℂ) * (𝓕 (h₂.toLp f) : Lp ℂ 2 volume) x) =
    ∫ x, (g x : ℂ) * 𝓕 f x at h
  simpa only [Complex.real_smul] using h

theorem fourier_integral_memLp {f : FourierSpace → ℂ}
    (hf : Integrable f) (h₂ : MemLp f 2 volume) : MemLp (𝓕 f) 2 volume :=
  (Lp.memLp (𝓕 (h₂.toLp f))).ae_eq (fourier_L2_ae_eq_integral hf h₂)

theorem fourier_integral_norm_sq {f : FourierSpace → ℂ}
    (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    (∫ x, ‖𝓕 f x‖^2) = ∫ x, ‖f x‖^2 := by
  calc
    _ = ∫ x, ‖(𝓕 (h₂.toLp f) : Lp ℂ 2 volume) x‖^2 := by
      apply integral_congr_ae
      filter_upwards [fourier_L2_ae_eq_integral hf h₂] with x hx
      rw [hx]
    _ = ‖𝓕 (h₂.toLp f)‖^2 := (L2_norm_sq_integral _).symm
    _ = ‖h₂.toLp f‖^2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x, ‖f x‖^2 := by
      rw [L2_norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityWeight
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Plancherel energy for the partial Fourier transform in spacetime -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published


theorem velocityFourier_measurable {r : Velocity × FourierSpace → ℂ} (hr : Measurable r) :
    Measurable (velocityFourier r) := by
  have hm : Measurable (fun p : (Velocity × FourierSpace) × FourierSpace =>
      𝐞 (-inner ℝ p.2 p.1.2) • r (p.1.1,p.2)) := by
    have hc : Measurable (fun p : (Velocity × FourierSpace) × FourierSpace =>
        𝐞 (-inner ℝ p.2 p.1.2)) := by fun_prop
    exact hc.smul (hr.comp (measurable_fst.fst.prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

attribute [local irreducible] velocityFourier

theorem velocityFourier_fiber_energy {r : Velocity × FourierSpace → ℂ}
    (v : Velocity) (h₁ : Integrable (fun x => r (v,x)))
    (h₂ : MemLp (fun x => r (v,x)) 2 volume) :
    (∫ x : FourierSpace, ‖velocityFourier r (v,x)‖^2) = ∫ x : FourierSpace, ‖r (v,x)‖^2 :=
  by simpa only [velocityFourier] using fourier_integral_norm_sq h₁ h₂

theorem velocityFourier_fiber_memLp {r : Velocity × FourierSpace → ℂ}
    (v : Velocity) (h₁ : Integrable (fun x => r (v,x)))
    (h₂ : MemLp (fun x => r (v,x)) 2 volume) :
    MemLp (fun x => velocityFourier r (v,x)) 2 volume :=
  by simpa only [velocityFourier] using fourier_integral_memLp h₁ h₂

theorem velocityFourier_integrable_sq {r : Velocity × FourierSpace → ℂ}
    (hr : Measurable r) (h₁ : Integrable r) (h₂ : MemLp r 2 volume) :
    Integrable (fun p => ‖velocityFourier r p‖^2) := by
  have hi := (memLp_two_iff_integrable_sq_norm h₂.aestronglyMeasurable).mp h₂
  have hm : Measurable (fun p => ‖velocityFourier r p‖^2) :=
    (velocityFourier_measurable hr).norm.pow_const 2
  have hfiber : ∀ᵐ v ∂(volume : Measure Velocity),
      MemLp (fun x => r (v,x)) 2 volume := by
    filter_upwards [hi.prod_right_ae] with v hv
    have hmv : Measurable (fun x : FourierSpace => r (v,x)) := hr.comp measurable_prodMk_left
    exact (memLp_two_iff_integrable_sq_norm hmv.aestronglyMeasurable).mpr hv
  have he : ∀ᵐ v ∂(volume : Measure Velocity),
      (∫ x : FourierSpace, ‖velocityFourier r (v,x)‖^2) =
        ∫ x : FourierSpace, ‖r (v,x)‖^2 := by
    filter_upwards [h₁.prod_right_ae,hfiber] with v hv₁ hv₂
    exact velocityFourier_fiber_energy v hv₁ hv₂
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [h₁.prod_right_ae,hfiber] with v hv₁ hv₂
    have hv := velocityFourier_fiber_memLp v hv₁ hv₂
    exact (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  · apply hi.integral_norm_prod_left.congr
    filter_upwards [he] with v hv
    simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hv.symm

theorem velocityFourier_energy {r : Velocity × FourierSpace → ℂ}
    (hr : Measurable r) (h₁ : Integrable r) (h₂ : MemLp r 2 volume) :
    (∫ p, ‖velocityFourier r p‖^2) = ∫ p, ‖r p‖^2 := by
  have hi := (memLp_two_iff_integrable_sq_norm h₂.aestronglyMeasurable).mp h₂
  change (∫ p, ‖velocityFourier r p‖^2 ∂(volume.prod volume)) =
    ∫ p, ‖r p‖^2 ∂(volume.prod volume)
  rw [integral_prod _ (velocityFourier_integrable_sq hr h₁ h₂),integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [h₁.prod_right_ae,hi.prod_right_ae] with v hv₁ hv₂
  have hmv : Measurable (fun x : FourierSpace => r (v,x)) := hr.comp measurable_prodMk_left
  exact velocityFourier_fiber_energy v hv₁
    ((memLp_two_iff_integrable_sq_norm hmv.aestronglyMeasurable).mpr hv₂)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Velocity support is preserved by the partial spacetime Fourier transform -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

theorem velocityFourier_support {r : Velocity × FourierSpace → ℂ} {R : ℝ}
    (hs : ∀ᵐ p ∂(volume : Measure (Velocity × FourierSpace)), R < ‖p.1‖ → r p = 0) :
    ∀ᵐ v ∂(volume : Measure Velocity), R < ‖v‖ →
      ∀ k, velocityFourier r (v,k) = 0 := by
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with v hv
  intro hR k
  have hz : (fun x : FourierSpace => r (v,x)) =ᵐ[volume] 0 := by
    filter_upwards [hv] with x hx
    exact hx hR
  calc
    _ = 𝓕 (0 : FourierSpace → ℂ) k := Real.fourier_congr_ae hz k
    _ = 0 := by rw [Real.fourier_eq]; simp

end BoltzmannNonuniqueness.Published

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

/-! # Uniformly integrable families admit bounded truncations without spatial tightness -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem uniform_value_truncation (f : ℕ → X → ℂ) (hf : ∀ n, Measurable (f n))
    (hui : UniformIntegrable f 1 μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∃ u : ℕ → X → ℂ,
      (∀ n, Measurable (u n)) ∧ (∀ n x, ‖u n x‖ ≤ C) ∧
      (∀ n x, f n x = 0 → u n x = 0) ∧
      (∀ n x, ‖u n x‖ ≤ ‖f n x‖) ∧
      (∀ n, eLpNorm (f n-u n) 1 μ ≤ ε) := by
  obtain ⟨C,hC⟩ := hui.spec (by norm_num) (by norm_num) hε
  let u (n : ℕ) : X → ℂ := {x | ‖f n x‖₊ < C}.indicator (f n)
  have hm n : MeasurableSet {x | ‖f n x‖₊ < C} :=
    measurableSet_lt (hf n).nnnorm measurable_const
  refine ⟨C,u,fun n => (hf n).indicator (hm n),?_,?_,?_,?_⟩
  · intro n x
    by_cases hx : ‖f n x‖₊ < C
    · simpa [u,hx] using (show ‖f n x‖ ≤ (C:ℝ) by exact_mod_cast le_of_lt hx)
    · simp [u,hx]
  · intro n x hx
    simp [u,hx]
  · intro n x
    by_cases ht : ‖f n x‖₊ < C <;> simp [u,ht]
  · intro n
    have he : f n-u n = {x | C ≤ ‖f n x‖₊}.indicator (f n) := by
      funext x
      by_cases ht : ‖f n x‖₊ < C
      · simp [u,ht,not_le.mpr ht]
      · simp [u,ht,le_of_not_gt ht]
    rw [he]
    exact hC n

end BoltzmannNonuniqueness.Published

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

/-! # Countably many L² approximations with uniform vanishing L¹ errors -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

theorem truncationError_pos (m : ℕ) : 0 < truncationError m := by
  unfold truncationError
  positivity

theorem truncationError_tendsto : Tendsto truncationError atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocitySmoothingError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The pointwise Fourier estimate for the actual velocity multiplier -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace BoltzmannNonuniqueness.Published

attribute [local irreducible] complexVelocityMultiplier velocityMultiplierMass velocityMultiplier

theorem velocity_spectral_bound (R : ℝ) (n : ℕ) (k : SpaceTime)
    (r : Lp ℂ 2 (volume.restrict (Metric.closedBall (0 : Velocity) R))) :
    ‖∫ v in Metric.closedBall (0 : Velocity) R, complexVelocityMultiplier n k v*r v‖^2 ≤
      velocityMultiplierMass R n k * ‖r‖^2 := by
  let μ : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  have : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  have hmc : Continuous (fun v => conj (complexVelocityMultiplier n k v)) :=
    Complex.continuous_conj.comp ((complexVelocityMultiplier_continuous n).comp
      (continuous_const.prodMk continuous_id))
  have hm : MemLp (fun v => conj (complexVelocityMultiplier n k v)) 2 μ :=
    (memLp_const (1 : ℂ)).of_le hmc.aestronglyMeasurable
      (ae_of_all _ (fun v => by simpa using complexVelocityMultiplier_norm_le_one n k v))
  let a : Lp ℂ 2 μ := hm.toLp _
  have ha : (a : Velocity → ℂ) =ᵐ[μ] fun v => conj (complexVelocityMultiplier n k v) :=
    MemLp.coeFn_toLp _
  have he : (∫ v, complexVelocityMultiplier n k v*r v ∂μ) = inner ℂ a r := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha] with v hv
    simp [hv,RCLike.inner_apply,mul_comm]
  have hn : ‖a‖^2 = velocityMultiplierMass R n k := by
    rw [L2_norm_sq_integral,velocityMultiplierMass]
    apply integral_congr_ae
    filter_upwards [ha] with v hv
    rw [hv,Complex.norm_conj,complexVelocityMultiplier_norm_sq]
  change ‖∫ v, complexVelocityMultiplier n k v*r v ∂μ‖^2 ≤ _
  rw [he,← hn,← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm a r) 2

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedCollisionHistories
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # The Fourier multiplier of the exponentially damped characteristic integral -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem dampedCharacter_eq (β s : ℝ) :
    dampedCharacter β s = Complex.exp ((-(1+Complex.I*β))*s) := by
  rw [dampedCharacter,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_dampedCharacter (β : ℝ) :
    (∫ s in Ioi (0 : ℝ), dampedCharacter β s) = (1+Complex.I*β)⁻¹ := by
  simp_rw [dampedCharacter_eq]
  rw [integral_exp_mul_complex_Ioi (by norm_num : (-(1+Complex.I*β)).re < 0)]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div_neg_eq,one_div]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Integrability along the actual damped transport lines in Fourier coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem lineShear_measurePreserving (w : FourierSpace) (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (lineShear w) (μ.prod (volume : Measure FourierSpace)) (μ.prod volume) := by
  unfold lineShear
  apply (MeasurePreserving.id μ).skew_product (g := fun s x => x-s • w)
    (μc := (volume : Measure FourierSpace)) (μd := (volume : Measure FourierSpace))
  · fun_prop
  · exact ae_of_all _ (fun s => (measurePreserving_add_right volume (-(s • w))).map_eq)

theorem dampedLine_integrable {f : FourierSpace → ℂ} (hf : Integrable f) (w : FourierSpace) :
    Integrable (fun p : ℝ × FourierSpace => Real.exp (-p.1) • f (p.2-p.1 • w))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  exact (lineShear_measurePreserving w _).integrable_comp_of_integrable
    ((integrableOn_exp_neg_Ioi 0).smul_prod hf)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Passing the Fourier integral through damped transport along a line -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

attribute [local irreducible] dampedLineResolvent

theorem fourierLineKernel_integrable {f : FourierSpace → ℂ} (hf : Integrable f)
    (w k : FourierSpace) : Integrable (fourierLineKernel f w k)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hb := dampedLine_integrable hf w
  apply hb.norm.mono'
  · have hc : Measurable (fun p : ℝ × FourierSpace => 𝐞 (-inner ℝ p.2 k)) := by
      fun_prop
    exact hc.aestronglyMeasurable.smul hb.aestronglyMeasurable
  · exact ae_of_all _ (fun p => by
      simp only [fourierLineKernel,Circle.norm_smul]
      exact le_rfl)

theorem fourier_dampedLine_integral {f : FourierSpace → ℂ} (hf : Integrable f)
    (w k : FourierSpace) :
    𝓕 (dampedLineResolvent f w) k =
      ∫ s in Ioi (0 : ℝ), Real.exp (-s) • 𝓕 (fun x => f (x-s • w)) k := by
  rw [Real.fourier_eq]
  calc
    _ = ∫ x : FourierSpace, ∫ s in Ioi (0 : ℝ), fourierLineKernel f w k (s,x) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change 𝐞 (-inner ℝ x k) • dampedLineResolvent f w x = _
        unfold dampedLineResolvent
        change ((𝐞 (-inner ℝ x k) : ℂ) *
          ∫ s in Ioi (0 : ℝ), Real.exp (-s) • f (x-s • w)) = _
        rw [← integral_const_mul]
        rfl)
    _ = ∫ s in Ioi (0 : ℝ), ∫ x : FourierSpace, fourierLineKernel f w k (s,x) :=
      (integral_integral_swap (f := fun s x => fourierLineKernel f w k (s,x))
        (fourierLineKernel_integrable hf w k)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun s => by
        change (∫ x : FourierSpace, fourierLineKernel f w k (s,x)) =
          Real.exp (-s) • 𝓕 (fun x => f (x-s • w)) k
        rw [Real.fourier_eq,← integral_smul]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by
          exact smul_comm (𝐞 (-inner ℝ x k)) (Real.exp (-s)) (f (x-s • w))))

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedBranchingBlocks
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # The actual Fourier multiplier of a damped characteristic line -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem fourier_line_translation (f : FourierSpace → ℂ) (w k : FourierSpace) (s : ℝ) :
    𝓕 (fun x => f (x-s • w)) k = 𝐞 (-s*inner ℝ w k) • 𝓕 f k := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    𝐞 (volume : Measure FourierSpace) (innerₗ FourierSpace) f ((-s) • w)) k
  change 𝓕 (fun x => f (x+(-s) • w)) k = 𝐞 (inner ℝ ((-s) • w) k) • 𝓕 f k at h
  simp only [real_inner_smul_left] at h
  simpa only [neg_smul,sub_eq_add_neg,neg_mul] using h

theorem damped_phase_character (a s : ℝ) (z : ℂ) :
    Real.exp (-s) • (𝐞 (-s*a) • z) = dampedCharacter (2*Real.pi*a) s*z := by
  change (Real.exp (-s) : ℂ) *
    (Complex.exp (↑(2*Real.pi*(-s*a)) * Complex.I) * z) =
    ((Real.exp (-s) : ℂ) * Complex.exp (-Complex.I * (↑(2*Real.pi*a) * ↑s))) * z
  have he : (↑(2*Real.pi*(-s*a)) : ℂ) * Complex.I =
      -Complex.I * (↑(2*Real.pi*a) * ↑s) := by push_cast <;> ring
  rw [he]
  exact (mul_assoc _ _ _).symm

theorem fourier_dampedLine {f : FourierSpace → ℂ} (hf : Integrable f) (w k : FourierSpace) :
    𝓕 (dampedLineResolvent f w) k =
      (1+Complex.I*(2*Real.pi*inner ℝ w k))⁻¹ * 𝓕 f k := by
  rw [fourier_dampedLine_integral hf]
  simp_rw [fourier_line_translation,damped_phase_character]
  rw [integral_mul_const,integral_dampedCharacter]
  push_cast
  rfl

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ComplexWeakL2Diagonal
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Closed norm bounds pass to weak complex L2 limits -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem complex_weak_norm_le {u : ℕ → Lp ℂ 2 μ} {g : Lp ℂ 2 μ} {C : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ C)
    (hw : ∀ h : Lp ℂ 2 μ,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h))) : ‖g‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hu 0)
  have hb : ‖inner ℂ g g‖ ≤ C*‖g‖ := le_of_tendsto (hw g).norm
    (Eventually.of_forall (fun n => (norm_inner_le_norm (u n) g).trans
      (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg g))))
  simp only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg g)] at hb
  nlinarith [norm_nonneg g]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Restricting the complex L2 norm to a physical window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem complexL2Restriction_ae (K : Set FourierSpace) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    (complexL2Restriction K a : FourierSpace → ℂ) =ᵐ[volume.restrict K] a :=
  MemLp.coeFn_toLp _

theorem complexL2Restriction_sub (K : Set FourierSpace)
    (a b : Lp ℂ 2 (volume : Measure FourierSpace)) :
    complexL2Restriction K (a-b) = complexL2Restriction K a-complexL2Restriction K b := by
  apply Lp.ext
  filter_upwards [complexL2Restriction_ae K (a-b),
    ae_restrict_of_ae (Lp.coeFn_sub a b),
    Lp.coeFn_sub (complexL2Restriction K a) (complexL2Restriction K b),
    complexL2Restriction_ae K a,complexL2Restriction_ae K b] with x h hsub hright ha hb
  simp only [Pi.sub_apply] at hsub hright
  rw [h,hsub,hright,ha,hb]

theorem complexL2Restriction_norm_le (K : Set FourierSpace)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) : ‖complexL2Restriction K a‖ ≤ ‖a‖ := by
  rw [complexL2Restriction,Lp.norm_toLp,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp a).eLpNorm_ne_top
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem complexL2Restriction_norm_sq (K : Set FourierSpace)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    ‖complexL2Restriction K a‖^2 = ∫ x in K, ‖a x‖^2 := by
  rw [L2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [complexL2Restriction_ae K a] with x hx
  rw [hx]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A common complex weak subsequence for the countably many Fourier truncations -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace.CountablyGenerated X] [SFinite μ]

theorem exists_common_weak_complex_L2_subsequence (u : ℕ → ℕ → Lp ℂ 2 μ) (C : ℕ → ℝ)
    (hu : ∀ m n, ‖u m n‖ ≤ C m) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Lp ℂ 2 μ), StrictMono φ ∧
      ∀ m, ‖g m‖ ≤ C m ∧ ∀ h : Lp ℂ 2 μ,
        Tendsto (fun n => inner ℂ (u m (φ n)) h) atTop (𝓝 (inner ℂ (g m) h)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let K (m : ℕ) : Set (WeakDual ℂ (Lp ℂ 2 μ)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 (C m)
  have hK m : IsCompact (K m) := WeakDual.isCompact_closedBall 0 (C m)
  have : ∀ m, CompactSpace (K m) := fun m => isCompact_iff_compactSpace.mp (hK m)
  have : ∀ m, TopologicalSpace.MetrizableSpace (K m) :=
    fun m => WeakDual.metrizable_of_isCompact ℂ (Lp ℂ 2 μ) (K m) (hK m)
  let v : ℕ → ∀ m, K m := fun n m =>
    ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ) (u m n)),by
      simpa [K,Metric.mem_closedBall,dist_zero_right] using hu m n⟩
  have hseq : IsSeqCompact (univ : Set (∀ m, K m)) := isCompact_univ.isSeqCompact
  obtain ⟨l,-,φ,hφ,hl⟩ := hseq (fun n => mem_univ (v n))
  let g : ℕ → Lp ℂ 2 μ := fun m =>
    (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm (l m).val.toStrongDual
  refine ⟨φ,g,hφ,fun m => ⟨?_,fun h => ?_⟩⟩
  · have hnorm : ‖(l m).val.toStrongDual‖ ≤ C m := by
      have hp := (l m).property
      change dist (l m).val.toStrongDual 0 ≤ C m at hp
      simpa only [dist_zero_right] using hp
    simpa only [g,LinearIsometryEquiv.norm_map] using hnorm
  · have ht := ((WeakDual.eval_continuous h).comp
        (continuous_subtype_val.comp (continuous_apply m))).continuousAt.tendsto.comp hl
    simpa [v,g,InnerProductSpace.toDual_symm_apply,Function.comp_def] using ht

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalL1ApproximationLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local strong L2 convergence controls the local L1 seminorm -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem localL2_L1_bound (K : Set FourierSpace)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    eLpNorm (a : FourierSpace → ℂ) 1 (volume.restrict K) ≤
      ENNReal.ofReal ‖complexL2Restriction K a‖ * volume K ^ (1/2 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict K) (f := (a : FourierSpace → ℂ)) (p := 1) (q := 2)
    (by norm_num) (Lp.aestronglyMeasurable a).restrict
  have he : eLpNorm (a : FourierSpace → ℂ) 2 (volume.restrict K) =
      ENNReal.ofReal ‖complexL2Restriction K a‖ := by
    rw [ofReal_norm,complexL2Restriction,Lp.enorm_toLp]
  rw [he] at h
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

theorem localL2_L1_tendsto {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)}
    (K : Set FourierSpace) (hK : volume K < ⊤)
    (hu : Tendsto (fun n => ‖complexL2Restriction K (u n)‖) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n : FourierSpace → ℂ) 1 (volume.restrict K)) atTop (𝓝 0) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hu
  have hb := ENNReal.Tendsto.mul_const h
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity : (0:ℝ) ≤ 1/2) hK.ne))
  have hb' : Tendsto (fun n => ENNReal.ofReal ‖complexL2Restriction K (u n)‖ *
      volume K ^ (1/2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,ENNReal.ofReal_zero,zero_mul] using hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb'
    (fun _ => bot_le) (fun n => localL2_L1_bound K (u n))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform integral bounds on finite balls give a global integral bound -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

theorem lintegral_le_of_closedBall_bounds (f : FourierSpace → ℝ≥0∞) (B : ℝ≥0∞)
    (h : ∀ n : ℕ, (∫⁻ x in Metric.closedBall (0 : FourierSpace) n, f x) ≤ B) :
    (∫⁻ x, f x) ≤ B := by
  let μ := (volume : Measure FourierSpace).withDensity f
  have hm : Monotone (fun n : ℕ => Metric.closedBall (0 : FourierSpace) n) := by
    intro n m hnm
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hnm)
  have he : (∫⁻ x, f x) = μ (Set.univ : Set FourierSpace) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [he,← Metric.iUnion_closedBall_nat (0 : FourierSpace),hm.measure_iUnion]
  exact iSup_le (fun n => by simpa only [μ,withDensity_apply _ measurableSet_closedBall] using h n)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Global L1 bounds pass through local L1 convergence -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem localL1_global_bound {u : ℕ → FourierSpace → ℂ} {g : FourierSpace → ℂ}
    (hg : AEStronglyMeasurable g volume) (B : ℝ≥0∞)
    (hu : ∀ n, eLpNorm (u n) 1 volume ≤ B)
    (hc : ∀ K : Set FourierSpace, volume K < ⊤ →
      Tendsto (fun n => eLpNorm (u n-g) 1 (volume.restrict K)) atTop (𝓝 0))
    (hum : ∀ n, AEStronglyMeasurable (u n) volume) :
    eLpNorm g 1 volume ≤ B := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  apply lintegral_le_of_closedBall_bounds
  intro m
  let K := Metric.closedBall (0 : FourierSpace) (m : ℝ)
  have hK : volume K < ⊤ := measure_closedBall_lt_top
  have he n : eLpNorm g 1 (volume.restrict K) ≤
      eLpNorm (u n-g) 1 (volume.restrict K)+B := by
    have hid : g = (g-u n)+u n := by funext x; simp
    calc
      _ = eLpNorm ((g-u n)+u n) 1 (volume.restrict K) := by rw [← hid]
      _ ≤ eLpNorm (g-u n) 1 (volume.restrict K)+eLpNorm (u n) 1 (volume.restrict K) :=
        eLpNorm_add_le (hf := (hg.sub (hum n)).restrict) (hg := (hum n).restrict) (by norm_num)
      _ ≤ eLpNorm (u n-g) 1 (volume.restrict K)+B := by
        rw [eLpNorm_sub_comm]
        exact add_le_add_right ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hu n)) _
  have ht : Tendsto (fun n => eLpNorm (u n-g) 1 (volume.restrict K)+B) atTop (𝓝 B) := by
    simpa using (hc K hK).add_const B
  have h := ge_of_tendsto ht (Eventually.of_forall he)
  simpa only [eLpNorm_one_eq_lintegral_enorm] using h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Local L1 convergence is stable under differences -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem eLpNorm_sub_triangle {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g h : X → ℂ) (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hhm : AEStronglyMeasurable h μ) : eLpNorm (f-h) 1 μ ≤ eLpNorm (f-g) 1 μ+eLpNorm (g-h) 1 μ := by
  have he : f-h = (f-g)+(g-h) := by ext x; simp
  rw [he]
  exact eLpNorm_add_le (hf := hfm.sub hgm) (hg := hgm.sub hhm) (by norm_num)

theorem localL1_difference_tendsto {u v : ℕ → FourierSpace → ℂ}
    {g h : FourierSpace → ℂ} (K : Set FourierSpace)
    (hu : Tendsto (fun n => eLpNorm (u n-g) 1 (volume.restrict K)) atTop (𝓝 0))
    (hv : Tendsto (fun n => eLpNorm (v n-h) 1 (volume.restrict K)) atTop (𝓝 0))
    (hum : ∀ n, AEStronglyMeasurable (u n) volume) (hvm : ∀ n, AEStronglyMeasurable (v n) volume)
    (hgm : AEStronglyMeasurable g volume) (hhm : AEStronglyMeasurable h volume) :
    Tendsto (fun n => eLpNorm ((u n-v n)-(g-h)) 1 (volume.restrict K)) atTop (𝓝 0) := by
  have he n : (u n-v n)-(g-h) = (u n-g)-(v n-h) := by ext x; simp only [Pi.sub_apply] <;> ring
  have hb n : eLpNorm ((u n-v n)-(g-h)) 1 (volume.restrict K) ≤
      eLpNorm (u n-g) 1 (volume.restrict K)+eLpNorm (v n-h) 1 (volume.restrict K) := by
    rw [he]
    exact eLpNorm_sub_le (hf := ((hum n).sub hgm).restrict) (hg := ((hvm n).sub hhm).restrict) (by norm_num)
  have ht : Tendsto (fun n => eLpNorm (u n-g) 1 (volume.restrict K)+
      eLpNorm (v n-h) 1 (volume.restrict K)) atTop (𝓝 0) := by simpa using hu.add hv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hb

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Limits of uniform L1 approximations are Cauchy in global L1 -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem localL1_approximation_difference_bound
    (f : ℕ → FourierSpace → ℂ) (u : ℕ → ℕ → FourierSpace → ℂ)
    (g : ℕ → FourierSpace → ℂ) (hg : ∀ m, Integrable (g m))
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m)
    (he : ∀ m n, eLpNorm (f n-u m n) 1 volume ≤ ENNReal.ofReal (δ m))
    (hc : ∀ m (K : Set FourierSpace), volume K < ⊤ →
      Tendsto (fun n => eLpNorm (u m n-g m) 1 (volume.restrict K)) atTop (𝓝 0))
    (hfm : ∀ n, AEStronglyMeasurable (f n) volume) (hum : ∀ m n, AEStronglyMeasurable (u m n) volume)
    (m k : ℕ) : eLpNorm (g m-g k) 1 volume ≤ ENNReal.ofReal (δ m+δ k) := by
  apply localL1_global_bound ((hg m).sub (hg k)).aestronglyMeasurable
  · intro n
    have h := eLpNorm_sub_triangle volume (u m n) (f n) (u k n) (hum m n) (hfm n) (hum k n)
    rw [eLpNorm_sub_comm (u m n) (f n)] at h
    apply h.trans
    simpa only [ENNReal.ofReal_add (hδ m) (hδ k)] using add_le_add (he m n) (he k n)
  · intro K hK
    exact localL1_difference_tendsto K (hc m K hK) (hc k K hK) (hum m) (hum k) (hg m).1 (hg k).1
  · exact fun n => (hum m n).sub (hum k n)

theorem localL1_approximation_cauchy
    (f : ℕ → FourierSpace → ℂ) (u : ℕ → ℕ → FourierSpace → ℂ)
    (g : ℕ → FourierSpace → ℂ) (hg : ∀ m, Integrable (g m))
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m) (hδ0 : Tendsto δ atTop (𝓝 0))
    (he : ∀ m n, eLpNorm (f n-u m n) 1 volume ≤ ENNReal.ofReal (δ m))
    (hc : ∀ m (K : Set FourierSpace), volume K < ⊤ →
      Tendsto (fun n => eLpNorm (u m n-g m) 1 (volume.restrict K)) atTop (𝓝 0))
    (hfm : ∀ n, AEStronglyMeasurable (f n) volume) (hum : ∀ m n, AEStronglyMeasurable (u m n) volume) :
    CauchySeq (fun m => (hg m).toL1 (g m)) := by
  have hb m k := localL1_approximation_difference_bound f u g hg δ hδ he hc hfm hum m k
  have hd m k : dist ((hg m).toL1 (g m)) ((hg k).toL1 (g k)) ≤ δ m+δ k := by
    apply (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hδ m) (hδ k))).mp
    rw [dist_eq_norm,L1.ofReal_norm_sub_eq_lintegral]
    have hae : (fun x => ‖(hg m).toL1 (g m) x-(hg k).toL1 (g k) x‖ₑ) =ᵐ[volume]
        (fun x => ‖(g m-g k) x‖ₑ) := by
      filter_upwards [(hg m).coeFn_toL1,(hg k).coeFn_toL1] with x hm hk
      simp only [hm,hk,Pi.sub_apply]
    rw [lintegral_congr_ae hae]
    simpa only [eLpNorm_one_eq_lintegral_enorm] using hb m k
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hδ0.eventually (gt_mem_nhds (half_pos hε)))
  exact ⟨N,fun m hm k hk => (hd m k).trans_lt (by linarith [hN m hm,hN k hk])⟩

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Completing a sequence uniformly approximated by locally compact families -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem localL1_approximation_limit
    (f : ℕ → FourierSpace → ℂ) (u : ℕ → ℕ → FourierSpace → ℂ)
    (g : ℕ → FourierSpace → ℂ) (hg : ∀ m, Integrable (g m))
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 ≤ δ m) (hδ0 : Tendsto δ atTop (𝓝 0))
    (he : ∀ m n, eLpNorm (f n-u m n) 1 volume ≤ ENNReal.ofReal (δ m))
    (hc : ∀ m (K : Set FourierSpace), volume K < ⊤ →
      Tendsto (fun n => eLpNorm (u m n-g m) 1 (volume.restrict K)) atTop (𝓝 0))
    (hfm : ∀ n, AEStronglyMeasurable (f n) volume) (hum : ∀ m n, AEStronglyMeasurable (u m n) volume) :
    ∃ q : Lp ℂ 1 (volume : Measure FourierSpace),
      ∀ K : Set FourierSpace, volume K < ⊤ →
        Tendsto (fun n => eLpNorm (f n-(q : FourierSpace → ℂ)) 1 (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨q,hq⟩ := cauchySeq_tendsto_of_complete
    (localL1_approximation_cauchy f u g hg δ hδ hδ0 he hc hfm hum)
  have hq0 : Tendsto (fun m => eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume) atTop (𝓝 0) := by
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hq.sub_const q).norm)
    have heq m : ENNReal.ofReal ‖(hg m).toL1 (g m)-q‖ = eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume := by
      rw [L1.ofReal_norm_sub_eq_lintegral,
        eLpNorm_one_eq_lintegral_enorm]
      apply lintegral_congr_ae
      filter_upwards [(hg m).coeFn_toL1] with x hx
      simp only [hx,Pi.sub_apply]
    simpa only [Function.comp_def,sub_self,norm_zero,ENNReal.ofReal_zero,heq] using ht
  have herror : Tendsto (fun m => ENNReal.ofReal (δ m)+eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero,zero_add] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hδ0).add hq0
  refine ⟨q,fun K hK => ?_⟩
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hh : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨m,hm⟩ := (ENNReal.tendsto_nhds_zero.mp herror (ε/2) hh).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hc m K hK) (ε/2) hh] with n hn
  calc
    eLpNorm (f n-(q : FourierSpace → ℂ)) 1 (volume.restrict K) ≤
        eLpNorm (f n-u m n) 1 (volume.restrict K)+eLpNorm (u m n-(q : FourierSpace → ℂ)) 1 (volume.restrict K) :=
      eLpNorm_sub_triangle _ _ _ _ (hfm n).restrict (hum m n).restrict (Lp.aestronglyMeasurable q).restrict
    _ ≤ ENNReal.ofReal (δ m)+(eLpNorm (u m n-g m) 1 (volume.restrict K)+eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume) := by
      apply add_le_add ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (he m n))
      exact (eLpNorm_sub_triangle _ _ _ _ (hum m n).restrict (hg m).1.restrict
        (Lp.aestronglyMeasurable q).restrict).trans
        (add_le_add le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self))
    _ = (ENNReal.ofReal (δ m)+eLpNorm (g m-(q : FourierSpace → ℂ)) 1 volume)+eLpNorm (u m n-g m) 1 (volume.restrict K) := by ac_rfl
    _ ≤ ε/2+ε/2 := add_le_add hm hn
    _ = ε := ENNReal.add_halves ε

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityAverageDifference
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The complex velocity-line average is an L1 contraction -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem integral_norm_partial_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X × Y → ℂ} (hf : Integrable f (μ.prod ν)) :
    (∫ y, ‖∫ x, f (x,y) ∂μ‖ ∂ν) ≤ ∫ p, ‖f p‖ ∂(μ.prod ν) := by
  calc
    _ ≤ ∫ y, ∫ x, ‖f (x,y)‖ ∂μ ∂ν :=
      integral_mono hf.integral_prod_right.norm hf.norm.integral_prod_right
        (fun y => norm_integral_le_integral_norm _)
    _ = _ := (integral_prod_symm _ hf.norm).symm

theorem velocityLineShear_integral_norm {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (s : ℝ) :
    (∫ p, ‖r (velocityLineShear s p)‖) = ∫ p, ‖r p‖ := by
  have hp := velocityLineShear_measurePreserving s
  have hm : AEStronglyMeasurable (fun p => ‖r p‖) (Measure.map (velocityLineShear s) volume) := by
    rw [hp.map_eq]
    exact hr.norm.aestronglyMeasurable
  have he := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at he
  exact he.symm

theorem velocityLineResolvent_L1_le {r : Velocity × FourierSpace → ℂ} (hr : Integrable r) :
    (∫ p, ‖velocityLineResolvent r p‖) ≤ ∫ p, ‖r p‖ := by
  have h := integral_norm_partial_le (velocityLine_integrable hr)
  calc
    _ ≤ ∫ q : ℝ × (Velocity × FourierSpace),
        ‖Real.exp (-q.1) • r (velocityLineShear q.1 q.2)‖
        ∂((volume.restrict (Ioi 0)).prod volume) := h
    _ = ∫ s in Ioi (0 : ℝ), Real.exp (-s)*(∫ p, ‖r p‖) := by
      rw [integral_prod _ (velocityLine_integrable hr).norm]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        rw [integral_const_mul,velocityLineShear_integral_norm hr])
    _ = _ := by rw [integral_mul_const,integral_exp_neg_Ioi_zero,one_mul]

theorem velocityLineAverage_L1_le {r : Velocity × FourierSpace → ℂ} (hr : Integrable r) :
    (∫ x, ‖velocityLineAverage r x‖) ≤ ∫ p, ‖r p‖ :=
  (integral_norm_partial_le (velocityLineResolvent_integrable hr)).trans
    (velocityLineResolvent_L1_le hr)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Linearity and L1 stability of the actual velocity average -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

theorem velocityLineResolvent_sub {r q : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (hq : Integrable q) :
    velocityLineResolvent (r-q) =ᵐ[volume] velocityLineResolvent r-velocityLineResolvent q := by
  filter_upwards [(velocityLine_integrable hr).prod_left_ae,
    (velocityLine_integrable hq).prod_left_ae] with p hp hq'
  change (∫ s in Ioi (0:ℝ), Real.exp (-s) • (r (velocityLineShear s p)-q (velocityLineShear s p))) = _
  simp_rw [smul_sub]
  exact integral_sub hp hq'

theorem velocityLineAverage_sub {r q : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (hq : Integrable q) :
    velocityLineAverage (r-q) =ᵐ[volume] velocityLineAverage r-velocityLineAverage q := by
  have he := (Measure.measurePreserving_swap (μ := (volume : Measure FourierSpace))
    (ν := (volume : Measure Velocity))).quasiMeasurePreserving.ae_eq_comp (velocityLineResolvent_sub hr hq)
  filter_upwards [Measure.ae_ae_of_ae_prod he,
    (velocityLineResolvent_integrable hr).prod_left_ae,
    (velocityLineResolvent_integrable hq).prod_left_ae] with x hx hri hqi
  simp only [Function.comp_apply,Prod.swap_prod_mk,Pi.sub_apply] at hx
  change (∫ v, velocityLineResolvent (r-q) (v,x)) = _
  rw [integral_congr_ae hx,integral_sub hri hqi]
  rfl

theorem velocityLineAverage_eLpNorm_le {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) :
    eLpNorm (velocityLineAverage r) 1 volume ≤ eLpNorm r 1 volume := by
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (velocityLineAverage_integrable hr),
    ← ofReal_integral_norm_eq_lintegral_enorm hr]
  exact ENNReal.ofReal_le_ofReal (velocityLineAverage_L1_le hr)

theorem velocityLineAverage_difference_le {r q : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (hq : Integrable q) :
    eLpNorm (velocityLineAverage r-velocityLineAverage q) 1 volume ≤
      eLpNorm (r-q) 1 volume := by
  rw [← eLpNorm_congr_ae (velocityLineAverage_sub hr hq)]
  exact velocityLineAverage_eLpNorm_le (hr.sub hq)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticWindowL1
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measure-preserving coordinates for the partial Fourier argument -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.Published

theorem kineticFourier_measurePreserving :
    MeasurePreserving kineticFourierEquiv (volume : Measure KineticPhase) volume := by
  have hp := (MeasurePreserving.id (volume : Measure Velocity)).prod spacetimeHilbert_measurePreserving
  have h := hp.comp (Measure.measurePreserving_swap (μ := (volume : Measure SpaceTime))
    (ν := (volume : Measure Velocity)))
  have he : (kineticFourierEquiv : KineticPhase → Velocity × FourierSpace) =
      Prod.map id spacetimeHilbertEquiv ∘ Prod.swap := rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using h

theorem kineticFourier_symm_measurePreserving :
    MeasurePreserving kineticFourierEquiv.symm (volume : Measure (Velocity × FourierSpace)) volume :=
  kineticFourier_measurePreserving.symm kineticFourierEquiv

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The Fourier-coordinate average is the original physical resolvent average -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem fourierSource_measurable {r : KineticPhase → ℝ} {ψ : Velocity → ℝ}
    (hr : Measurable r) (hψ : Measurable ψ) : Measurable (fourierSource r ψ) := by
  unfold fourierSource
  fun_prop

theorem fourierSource_resolvent (r : KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (v : Velocity) (z : SpaceTime) :
    velocityLineResolvent (fourierSource r ψ) (v,spacetimeHilbertEquiv z) =
      (ψ v*transportResolvent r (z,v) : ℝ) := by
  change (∫ s in Ioi (0 : ℝ), Real.exp (-s) •
    fourierSource r ψ (v,spacetimeHilbertEquiv z-s • characteristicDirection v)) = _
  calc
    _ = ∫ s in Ioi (0 : ℝ),
        ((Real.exp (-s)*(ψ v*r ((z.1-s,z.2-s • v),v)) : ℝ) : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => by
        dsimp only
        rw [← spacetimeHilbert_translation z s v]
        simp only [fourierSource,spacetimeHilbertEquiv,MeasurableEquiv.coe_toLp,
          WithLp.ofLp_toLp,Complex.real_smul,Complex.ofReal_mul])
    _ = ((∫ s in Ioi (0 : ℝ), Real.exp (-s)*(ψ v*r ((z.1-s,z.2-s • v),v)) : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = _ := by
      congr 1
      unfold transportResolvent
      rw [← restrict_Ioi_eq_restrict_Ici,← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => by ring)

theorem fourierSource_average (r : KineticPhase → ℝ) (ψ : Velocity → ℝ) (z : SpaceTime) :
    velocityLineAverage (fourierSource r ψ) (spacetimeHilbertEquiv z) =
      (resolventAverage r ψ z : ℂ) := by
  change (∫ v, velocityLineResolvent (fourierSource r ψ) (v,spacetimeHilbertEquiv z)) = _
  simp_rw [fourierSource_resolvent]
  exact integral_complex_ofReal

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_InverseFourierL2
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-! # The inverse Fourier integral agrees with the inverse L2 transform -/
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap Topology
namespace BoltzmannNonuniqueness.Published

theorem inverseFourier_L2_pairing (a : Lp ℂ 2 (volume : Measure FourierSpace))
    (g : 𝓢(FourierSpace, ℂ)) :
    (∫ x, g x * (𝓕⁻ a : Lp ℂ 2 volume) x) = ∫ x, (𝓕⁻ g) x * a x := by
  have h := congrArg (fun T : 𝓢'(FourierSpace, ℂ) => T g)
    (Lp.fourierInv_toTemperedDistribution_eq a)
  simpa only [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] using h.symm

theorem inverseFourier_integral_pairing {f : FourierSpace → ℂ} (hf : Integrable f)
    (g : 𝓢(FourierSpace, ℂ)) :
    (∫ x, g x * 𝓕⁻ f x) = ∫ x, (𝓕⁻ g) x * f x := by
  have he : (-innerₗ FourierSpace).flip = -innerₗ FourierSpace := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact congrArg Neg.neg (real_inner_comm x y)
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure FourierSpace))
    (ν := (volume : Measure FourierSpace)) (L := -innerₗ FourierSpace)
    Real.continuous_fourierChar continuous_inner.neg g.integrable hf
  rw [he] at h
  have h' : (∫ x, g x * 𝓕⁻ f x) = ∫ x, 𝓕⁻ (g : FourierSpace → ℂ) x * f x := by
    simpa only [Real.fourierInv_eq,VectorFourier.fourierIntegral,LinearMap.neg_apply,
      neg_neg,smul_eq_mul,innerₗ_apply_apply] using h.symm
  simpa only [← SchwartzMap.fourierInv_coe] using h'

theorem inverseFourier_L2_ae_eq_integral {f : FourierSpace → ℂ}
    (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    (fun x => (𝓕⁻ (h₂.toLp f) : Lp ℂ 2 volume) x) =ᵐ[volume] 𝓕⁻ f := by
  have hc : Continuous (𝓕⁻ f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner.neg hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ (h₂.toLp f))).locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
  let ψ : 𝓢(FourierSpace, ℂ) := hs'.toSchwartzMap hg'
  have h₁ := inverseFourier_L2_pairing (h₂.toLp f) ψ
  have h₂' : (∫ x, (𝓕⁻ ψ) x * (h₂.toLp f) x) = ∫ x, (𝓕⁻ ψ) x * f x := by
    apply integral_congr_ae
    filter_upwards [h₂.coeFn_toLp] with x hx
    rw [hx]
  have h := (h₁.trans h₂').trans (inverseFourier_integral_pairing hf ψ).symm
  change (∫ x, (g x : ℂ) * (𝓕⁻ (h₂.toLp f) : Lp ℂ 2 volume) x) =
    ∫ x, (g x : ℂ) * 𝓕⁻ f x at h
  simpa only [Complex.real_smul] using h

end BoltzmannNonuniqueness.Published

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

theorem uniformIntegrable_norm_domination (f : ℕ → X → ℝ) (g : ℕ → X → ℂ)
    (hf : UniformIntegrable f 1 μ) (hg : ∀ n, Measurable (g n))
    (D : ℝ≥0) (hd : ∀ n x, ‖g n x‖ ≤ (D : ℝ)*‖f n x‖) :
    UniformIntegrable g 1 μ := by
  have hnorm n (S : Set X) : eLpNorm (g n) 1 (μ.restrict S) ≤
      (D : ℝ≥0∞)*eLpNorm (f n) 1 (μ.restrict S) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (ae_of_all _ (hd n)) 1
  constructor
  · refine OAI.UnifIntegrable.of_enn (fun ε hε => ?_) (fun n => (hg n).aestronglyMeasurable)
    have hD1 : (D : ℝ≥0∞)+1 ≠ 0 := by simp
    have hDt : (D : ℝ≥0∞)+1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.one_ne_top⟩
    obtain ⟨δ,hδ,hδf⟩ := OAI.UnifIntegrable.enn_spec hf.1 (ε/((D : ℝ≥0∞)+1)) (ENNReal.div_pos hε.ne' hDt)
    refine ⟨δ,hδ,fun n S hS => ?_⟩
    calc eLpNorm (g n) 1 (μ.restrict S) ≤ (D : ℝ≥0∞)*eLpNorm (f n) 1 (μ.restrict S) := hnorm n S
      _ ≤ ((D : ℝ≥0∞)+1)*(ε/((D : ℝ≥0∞)+1)) := mul_le_mul' le_self_add (hδf n S hS)
      _ = ε := ENNReal.mul_div_cancel hD1 hDt
  · obtain ⟨C,hC⟩ := hf.2
    refine ⟨D*C,fun n => ?_⟩
    have h := hnorm n Set.univ
    simp only [Measure.restrict_univ] at h
    apply h.trans
    rw [ENNReal.coe_mul]
    gcongr
    exact hC n

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_FourierCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Finite-measure cutoffs of L2 Fourier data -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal
namespace BoltzmannNonuniqueness.Published

theorem complexL2Cutoff_ae (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    (complexL2Cutoff S hS a : FourierSpace → ℂ) =ᵐ[volume] S.indicator a :=
  MemLp.coeFn_toLp _

theorem complexL2Cutoff_integrable (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    Integrable (S.indicator a) := by
  have : Fact (volume S < ⊤) := ⟨hfinite⟩
  apply (integrable_indicator_iff hS).mpr
  exact ((Lp.memLp a).restrict S).integrable (by norm_num)

theorem fourierBandApprox_ae (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    (fun x => (𝓕⁻ (complexL2Cutoff S hS a) : Lp ℂ 2 (volume : Measure FourierSpace)) x) =ᵐ[volume]
      fourierBandApprox S a :=
  inverseFourier_L2_ae_eq_integral (complexL2Cutoff_integrable S hS hfinite a)
    ((Lp.memLp a).indicator hS)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A finite Fourier window evaluates by an L2 pairing -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ComplexConjugate RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem fourierBandApprox_pairing (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) (x : FourierSpace) :
    fourierBandApprox S a x = inner ℂ ((fourierBandTest_memLp S hS hfinite x).toLp
      (fourierBandTest S x)) a := by
  rw [fourierBandApprox,Real.fourierInv_eq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(fourierBandTest_memLp S hS hfinite x).coeFn_toLp] with k hk
  rw [hk]
  by_cases hks : k ∈ S
  · simp only [fourierBandTest,indicator_of_mem hks,RCLike.inner_apply]
    change (𝐞 (inner ℝ k x) : ℂ)*a k = a k*conj (𝐞 (-inner ℝ k x) : ℂ)
    rw [Circle.starRingEnd_addChar,neg_neg,mul_comm]
  · simp [fourierBandTest,hks,RCLike.inner_apply]

theorem fourierBandApprox_tendsto {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)}
    {g : Lp ℂ 2 (volume : Measure FourierSpace)}
    (hu : ∀ h : Lp ℂ 2 volume,
      Filter.Tendsto (fun n => inner ℂ (u n) h) Filter.atTop (nhds (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) (hfinite : volume S < ⊤) (x : FourierSpace) :
    Filter.Tendsto (fun n => fourierBandApprox S (u n) x) Filter.atTop
      (nhds (fourierBandApprox S g x)) := by
  simp_rw [fourierBandApprox_pairing S hS hfinite]
  have h := (Complex.continuous_conj.tendsto _).comp
    (hu ((fourierBandTest_memLp S hS hfinite x).toLp (fourierBandTest S x)))
  simpa only [Function.comp_def,inner_conj_symm] using h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform pointwise bounds on finite-frequency reconstructions -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform ComplexConjugate RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem fourierBandTest_norm_sq (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (x : FourierSpace) :
    ‖(fourierBandTest_memLp S hS hfinite x).toLp (fourierBandTest S x)‖^2 = volume.real S := by
  rw [L2_norm_sq_integral]
  calc
    _ = ∫ k, S.indicator (fun _ => (1 : ℝ)) k := by
      apply integral_congr_ae
      filter_upwards [(fourierBandTest_memLp S hS hfinite x).coeFn_toLp] with k hk
      rw [hk]
      by_cases hks : k ∈ S <;> simp [fourierBandTest,hks,Circle.norm_coe]
    _ = volume.real S := by rw [integral_indicator hS]; simp

theorem fourierBandApprox_norm_le (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) (x : FourierSpace) :
    ‖fourierBandApprox S a x‖ ≤ (volume.real S+1)*‖a‖ := by
  let q := (fourierBandTest_memLp S hS hfinite x).toLp (fourierBandTest S x)
  have hq : ‖q‖ ≤ volume.real S+1 := by
    have he := fourierBandTest_norm_sq S hS hfinite x
    change ‖q‖^2 = volume.real S at he
    nlinarith [sq_nonneg (‖q‖-1),norm_nonneg q]
  rw [fourierBandApprox_pairing S hS hfinite]
  exact (norm_inner_le_norm q a).trans
    (mul_le_mul_of_nonneg_right hq (norm_nonneg a))

theorem fourierBandApprox_continuous (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    Continuous (fourierBandApprox S a) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner.neg
    (complexL2Cutoff_integrable S hS hfinite a)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak L2 convergence becomes strong locally after a finite-frequency cutoff -/
noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform Topology
namespace BoltzmannNonuniqueness.Published

theorem fourierBandApprox_local_convergence
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ n, ‖u n‖ ≤ C) (hg : ‖g‖ ≤ C)
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) (hfinite : volume S < ⊤)
    (K : Set FourierSpace) (hK : volume K < ⊤) :
    Tendsto (fun n => ∫ x in K, ‖fourierBandApprox S (u n) x-fourierBandApprox S g x‖^2)
      atTop (𝓝 0) := by
  have : IsFiniteMeasure ((volume : Measure FourierSpace).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.ne
  let B := 2*(volume.real S+1)*C
  have hb n x : ‖fourierBandApprox S (u n) x-fourierBandApprox S g x‖ ≤ B := by
    have h₁ := fourierBandApprox_norm_le S hS hfinite (u n) x
    have h₂ := fourierBandApprox_norm_le S hS hfinite g x
    have hpos : 0 ≤ volume.real S+1 := by positivity
    have h₃ := mul_le_mul_of_nonneg_left (hu n) hpos
    have h₄ := mul_le_mul_of_nonneg_left hg hpos
    have ht := norm_sub_le (fourierBandApprox S (u n) x) (fourierBandApprox S g x)
    dsimp [B]
    linarith
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have ht := tendsto_integral_of_dominated_convergence (μ := volume.restrict K)
    (fun _ : FourierSpace => B^2)
    (fun n => (((fourierBandApprox_continuous S hS hfinite (u n)).sub
      (fourierBandApprox_continuous S hS hfinite g)).norm.pow 2).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb n x) 2))
    (ae_of_all _ (fun x => by
      have hx := ((fourierBandApprox_tendsto hw S hS hfinite x).sub_const
        (fourierBandApprox S g x)).norm.pow 2
      simpa only [Pi.pow_apply,Pi.sub_apply,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using hx))
  simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The error of finite-frequency reconstruction is exactly its Fourier tail -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

theorem complexL2Cutoff_error (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    ‖a-complexL2Cutoff S hS a‖^2 = ∫ k in Sᶜ, ‖a k‖^2 := by
  rw [L2_norm_sq_integral,← integral_indicator hS.compl]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub a (complexL2Cutoff S hS a),complexL2Cutoff_ae S hS a] with k hk hc
  simp only [Pi.sub_apply] at hk
  rw [hk,hc]
  by_cases hks : k ∈ S <;> simp [hks]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Local norms of finite-frequency reconstruction errors -/
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped FourierTransform Topology
namespace BoltzmannNonuniqueness.Published

theorem inverseFourier_norm (a : Lp ℂ 2 (volume : Measure FourierSpace)) : ‖𝓕⁻ a‖ = ‖a‖ := by
  simpa only [fourier_fourierInv_eq] using (Lp.norm_fourier_eq (𝓕⁻ a)).symm

theorem inverseFourier_sub (a b : Lp ℂ 2 (volume : Measure FourierSpace)) :
    (𝓕⁻ (a-b) : Lp ℂ 2 volume) = 𝓕⁻ a-𝓕⁻ b :=
  (Lp.fourierTransformₗᵢ FourierSpace ℂ).symm.map_sub a b

theorem fourierReconstruction_error (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    ‖(𝓕⁻ a : Lp ℂ 2 volume)-𝓕⁻ (complexL2Cutoff S hS a)‖ =
      ‖a-complexL2Cutoff S hS a‖ := by
  rw [← inverseFourier_sub,inverseFourier_norm]

theorem fourierReconstruction_local_band_sq (S : Set FourierSpace) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (K : Set FourierSpace)
    (a b : Lp ℂ 2 (volume : Measure FourierSpace)) :
    ‖complexL2Restriction K ((𝓕⁻ (complexL2Cutoff S hS a) : Lp ℂ 2 volume)-
      𝓕⁻ (complexL2Cutoff S hS b))‖^2 =
      ∫ x in K, ‖fourierBandApprox S a x-fourierBandApprox S b x‖^2 := by
  rw [complexL2Restriction_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (𝓕⁻ (complexL2Cutoff S hS a))
    (𝓕⁻ (complexL2Cutoff S hS b))),ae_restrict_of_ae (fourierBandApprox_ae S hS hfinite a),
    ae_restrict_of_ae (fourierBandApprox_ae S hS hfinite b)] with x hx ha hb
  simp only [Pi.sub_apply] at hx
  rw [hx,ha,hb]

theorem fourierReconstruction_local_band_tendsto
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ n, ‖u n‖ ≤ C) (hg : ‖g‖ ≤ C)
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) (hfinite : volume S < ⊤)
    (K : Set FourierSpace) (hK : volume K < ⊤) :
    Tendsto (fun n => ‖complexL2Restriction K
      ((𝓕⁻ (complexL2Cutoff S hS (u n)) : Lp ℂ 2 volume)-𝓕⁻ (complexL2Cutoff S hS g))‖)
      atTop (𝓝 0) := by
  have h := (fourierBandApprox_local_convergence hC hu hg hw S hS hfinite K hK).sqrt
  simp_rw [← fourierReconstruction_local_band_sq S hS hfinite K,Real.sqrt_sq_eq_abs,
    abs_norm] at h
  simpa only [Real.sqrt_zero] using h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Fourier-window projections preserve weak convergence and closed norm bounds -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BoltzmannNonuniqueness.Published

theorem complexL2Cutoff_inner (S : Set FourierSpace) (hS : MeasurableSet S)
    (a b : Lp ℂ 2 (volume : Measure FourierSpace)) :
    inner ℂ (complexL2Cutoff S hS a) b = inner ℂ a (complexL2Cutoff S hS b) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [complexL2Cutoff_ae S hS a,complexL2Cutoff_ae S hS b] with x ha hb
  rw [ha,hb]
  by_cases hx : x ∈ S <;> simp [hx]

theorem complexL2Cutoff_weak_tendsto
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) (h : Lp ℂ 2 volume) :
    Tendsto (fun n => inner ℂ (complexL2Cutoff S hS (u n)) h) atTop
      (𝓝 (inner ℂ (complexL2Cutoff S hS g) h)) := by
  simpa only [complexL2Cutoff_inner] using hw (complexL2Cutoff S hS h)

theorem complexL2Cutoff_limit_bound
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (S : Set FourierSpace) (hS : MeasurableSet S) {C : ℝ}
    (hu : ∀ n, ‖complexL2Cutoff S hS (u n)‖ ≤ C) : ‖complexL2Cutoff S hS g‖ ≤ C :=
  complex_weak_norm_le hu (complexL2Cutoff_weak_tendsto hw S hS)

theorem complexL2Cutoff_compl (S : Set FourierSpace) (hS : MeasurableSet S)
    (a : Lp ℂ 2 (volume : Measure FourierSpace)) :
    a-complexL2Cutoff S hS a = complexL2Cutoff Sᶜ hS.compl a := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub a (complexL2Cutoff S hS a),complexL2Cutoff_ae S hS a,
    complexL2Cutoff_ae Sᶜ hS.compl a] with x hx hc hd
  simp only [Pi.sub_apply] at hx
  rw [hx,hc,hd]
  by_cases hxs : x ∈ S <;> simp [hxs]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform Fourier tails upgrade weak L2 convergence to local strong convergence -/
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped FourierTransform Topology
namespace BoltzmannNonuniqueness.Published

theorem inverseFourier_local_strong_of_weak_and_tails
    {u : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)} {g : Lp ℂ 2 volume}
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ n, ‖u n‖ ≤ C) (hg : ‖g‖ ≤ C)
    (hw : ∀ h : Lp ℂ 2 volume,
      Tendsto (fun n => inner ℂ (u n) h) atTop (𝓝 (inner ℂ g h)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ S : Set FourierSpace, ∃ hS : MeasurableSet S,
      volume S < ⊤ ∧ ∀ n, ‖u n-complexL2Cutoff S hS (u n)‖ ≤ ε)
    (K : Set FourierSpace) (hK : volume K < ⊤) :
    Tendsto (fun n => ‖complexL2Restriction K ((𝓕⁻ (u n) : Lp ℂ 2 volume)-𝓕⁻ g)‖)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨S,hS,hfinite,ht⟩ := htail (ε/4) (by positivity)
  have htg : ‖g-complexL2Cutoff S hS g‖ ≤ ε/4 := by
    rw [complexL2Cutoff_compl]
    apply complexL2Cutoff_limit_bound hw Sᶜ hS.compl
    intro n
    rw [← complexL2Cutoff_compl S hS (u n)]
    exact ht n
  have hb := fourierReconstruction_local_band_tendsto hC hu hg hw S hS hfinite K hK
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hb (ε/4) (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  let A := complexL2Restriction K (𝓕⁻ (u n))
  let B := complexL2Restriction K (𝓕⁻ (complexL2Cutoff S hS (u n)))
  let D := complexL2Restriction K (𝓕⁻ (complexL2Cutoff S hS g))
  let G := complexL2Restriction K (𝓕⁻ g)
  have hAB : ‖A-B‖ ≤ ε/4 := by
    dsimp [A,B]
    rw [← complexL2Restriction_sub]
    exact (complexL2Restriction_norm_le K _).trans
      ((fourierReconstruction_error S hS (u n)).le.trans (ht n))
  have hDG : ‖D-G‖ ≤ ε/4 := by
    dsimp [D,G]
    rw [norm_sub_rev,← complexL2Restriction_sub]
    exact (complexL2Restriction_norm_le K _).trans
      ((fourierReconstruction_error S hS g).le.trans htg)
  have hBD : ‖B-D‖ < ε/4 := by
    have hh := hN n hn
    rw [Real.dist_eq,sub_zero,abs_norm] at hh
    simpa only [complexL2Restriction_sub] using hh
  have htriangle : ‖A-G‖ ≤ ‖A-B‖+‖B-D‖+‖D-G‖ := by
    calc
      _ ≤ ‖A-B‖+‖B-G‖ := norm_sub_le_norm_sub_add_norm_sub A B G
      _ ≤ _ := by
        have h := norm_sub_le_norm_sub_add_norm_sub B D G
        linarith
  rw [Real.dist_eq,sub_zero,abs_norm,complexL2Restriction_sub]
  change ‖A-G‖ < ε
  linarith

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Fourier transformation commutes with an integrable velocity integral -/
noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem fourier_velocity_integral {F : Velocity × FourierSpace → ℂ} (hF : Integrable F)
    (k : FourierSpace) :
    𝓕 (fun x => ∫ v, F (v,x)) k = ∫ v, 𝓕 (fun x => F (v,x)) k := by
  have hi : Integrable (fun p : Velocity × FourierSpace =>
      𝐞 (-inner ℝ p.2 k) • F p) := by
    apply hF.norm.mono'
    · have hm : Measurable (fun p : Velocity × FourierSpace => 𝐞 (-inner ℝ p.2 k)) := by
        fun_prop
      exact hm.aestronglyMeasurable.smul hF.aestronglyMeasurable
    · exact ae_of_all _ (fun p => (Circle.norm_smul _ _).le)
  rw [Real.fourier_eq]
  calc
    _ = ∫ x : FourierSpace, ∫ v : Velocity, 𝐞 (-inner ℝ x k) • F (v,x) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change (𝐞 (-inner ℝ x k) : ℂ) * (∫ v, F (v,x)) = _
        rw [← integral_const_mul]
        rfl)
    _ = ∫ v : Velocity, ∫ x : FourierSpace, 𝐞 (-inner ℝ x k) • F (v,x) :=
      (integral_integral_swap (f := fun v x => 𝐞 (-inner ℝ x k) • F (v,x)) hi).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun v => (Real.fourier_eq _ _).symm)

theorem fourier_velocityLineAverage {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (k : FourierSpace) :
    𝓕 (velocityLineAverage r) k = ∫ v,
      (1+Complex.I*(2*Real.pi*inner ℝ (characteristicDirection v) k))⁻¹ *
        𝓕 (fun x => r (v,x)) k := by
  change 𝓕 (fun x => ∫ v, velocityLineResolvent r (v,x)) k = _
  rw [fourier_velocity_integral (velocityLineResolvent_integrable hr)]
  apply integral_congr_ae
  filter_upwards [hr.prod_right_ae] with v hv
  exact fourier_dampedLine hv (characteristicDirection v) k

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Bounded velocity tests preserve uniform integrability in Fourier coordinates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

theorem fourierSource_uniformIntegrable (r : ℕ → KineticPhase → ℝ)
    (hm : ∀ n, Measurable (r n)) (hui : UniformIntegrable r 1 volume)
    (ψ : Velocity → ℝ) (hψ : Continuous ψ) (hs : HasCompactSupport ψ) :
    UniformIntegrable (fun n => fourierSource (r n) ψ) 1 volume := by
  obtain ⟨C,hC⟩ := hψ.bounded_above_of_compact_support hs
  let D : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  apply uniformIntegrable_norm_domination (fun n => r n ∘ kineticFourierEquiv.symm)
    (fun n => fourierSource (r n) ψ)
    (uniformIntegrable_comp_equiv kineticFourierEquiv.symm kineticFourier_symm_measurePreserving r hui)
    (fun n => fourierSource_measurable (hm n) hψ.measurable) D
  intro n p
  change ‖((ψ p.1*r n (p.2.ofLp,p.1) : ℝ) : ℂ)‖ ≤ (D : ℝ)*‖r n (p.2.ofLp,p.1)‖
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_right ((hC p.1).trans (le_max_left _ _)) (abs_nonneg _)

theorem fourierSource_congr_ae {r q : KineticPhase → ℝ} (ψ : Velocity → ℝ)
    (he : r =ᵐ[volume] q) : fourierSource r ψ =ᵐ[volume] fourierSource q ψ := by
  have h := kineticFourier_symm_measurePreserving.quasiMeasurePreserving.ae_eq_comp he
  filter_upwards [h] with p hp
  change r (p.2.ofLp,p.1) = q (p.2.ofLp,p.1) at hp
  simp only [fourierSource,hp]

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalFrequencyWindow
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Physical spacetime frequencies in the velocity spectral estimate -/
noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem physicalFourierMultiplier (k : FourierSpace) (v : Velocity) :
    complexVelocityMultiplier 1 (physicalFourierFrequency k) v =
      (1+Complex.I*(2*Real.pi*inner ℝ (characteristicDirection v) k))⁻¹ := by
  rw [real_inner_comm k (characteristicDirection v),characteristicFrequency]
  simp only [complexVelocityMultiplier,physicalFourierFrequency,Prod.smul_fst,
    Prod.smul_snd,smul_eq_mul,real_inner_smul_left,Nat.cast_one]
  push_cast
  ring_nf

theorem velocity_spectral_integral_bound (R : ℝ) (k : SpaceTime)
    {f : Velocity → ℂ} (hf : MemLp f 2 (volume.restrict (Metric.closedBall (0 : Velocity) R))) :
    ‖∫ v in Metric.closedBall (0 : Velocity) R, complexVelocityMultiplier 1 k v*f v‖^2 ≤
      velocityMultiplierMass R 1 k * ∫ v in Metric.closedBall (0 : Velocity) R, ‖f v‖^2 := by
  let a := hf.toLp f
  have h₁ : (∫ v in Metric.closedBall (0 : Velocity) R, complexVelocityMultiplier 1 k v*f v) =
      ∫ v in Metric.closedBall (0 : Velocity) R, complexVelocityMultiplier 1 k v*a v := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with v hv
    rw [hv]
  have h₂ : (∫ v in Metric.closedBall (0 : Velocity) R, ‖f v‖^2) = ‖a‖^2 := by
    rw [L2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with v hv
    rw [hv]
  rw [h₁,h₂]
  exact velocity_spectral_bound R 1 k a

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Finite Fourier windows for the physical spacetime coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem physicalFourierFrequency_continuous : Continuous physicalFourierFrequency := by
  unfold physicalFourierFrequency
  fun_prop

theorem norm_le_physicalFourierFrequency (k : FourierSpace) :
    ‖k‖ ≤ ‖physicalFourierFrequency k‖ := by
  have h₁ : ‖(WithLp.ofLp k).1‖ ≤ ‖WithLp.ofLp k‖ := norm_fst_le _
  have h₂ : ‖(WithLp.ofLp k).2‖ ≤ ‖WithLp.ofLp k‖ := norm_snd_le _
  have hs := WithLp.prod_norm_sq_eq_of_L2 k
  change ‖k‖^2 = ‖(WithLp.ofLp k).1‖^2+‖(WithLp.ofLp k).2‖^2 at hs
  have hs₁ := pow_le_pow_left₀ (norm_nonneg (WithLp.ofLp k).1) h₁ 2
  have hs₂ := pow_le_pow_left₀ (norm_nonneg (WithLp.ofLp k).2) h₂ 2
  have hb : ‖k‖ ≤ 2*‖WithLp.ofLp k‖ := by
    nlinarith [norm_nonneg k,norm_nonneg (WithLp.ofLp k),norm_nonneg (WithLp.ofLp k).1,
      norm_nonneg (WithLp.ofLp k).2]
  rw [physicalFourierFrequency,norm_smul,Real.norm_of_nonneg (by positivity)]
  nlinarith [Real.pi_gt_three,norm_nonneg (WithLp.ofLp k)]

theorem physicalFrequencyWindow_finite (N : ℕ) : volume (physicalFrequencyWindow N) < ⊤ := by
  apply lt_of_le_of_lt (measure_mono (t := Metric.closedBall (0 : FourierSpace) N) ?_)
    (isCompact_closedBall _ _).measure_lt_top
  intro k hk
  exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using
    (norm_le_physicalFourierFrequency k).trans hk)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedMeshStep
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform L2 energy bounds for bounded-source velocity averages -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.Published

theorem bounded_integrable_square_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hi : Integrable f μ) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    (∫ x, ‖f x‖^2 ∂μ) ≤ B * ∫ x, ‖f x‖ ∂μ := by
  have hm := integrable_bounded_memLp_two hi hb
  calc
    _ ≤ ∫ x, B*‖f x‖ ∂μ := by
      apply integral_mono ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
        (hi.norm.const_mul B)
      intro x
      dsimp only
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem bounded_average_energy {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) {R B C : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0)
    (hC : (∫ p, ‖r p‖) ≤ C) :
    (∫ x, ‖velocityLineAverage r x‖^2) ≤
      volume.real (Metric.closedBall (0 : Velocity) R)*B*C := by
  have hav := velocityLineAverage_norm_le hb hs
  calc
    _ ≤ (volume.real (Metric.closedBall (0 : Velocity) R)*B)*∫ x, ‖velocityLineAverage r x‖ :=
      bounded_integrable_square_le (velocityLineAverage_integrable hr) hav
    _ ≤ _ := mul_le_mul_of_nonneg_left ((velocityLineAverage_L1_le hr).trans hC)
      (mul_nonneg (measureReal_nonneg) hB)

theorem bounded_average_L2_norm {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) {R B C : ℝ} (hB : 0 ≤ B)
    (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0)
    (hC : (∫ p, ‖r p‖) ≤ C) :
    ‖(velocityLineAverage_memLp_two hr hb hs).toLp (velocityLineAverage r)‖ ≤
      volume.real (Metric.closedBall (0 : Velocity) R)*B*C+1 := by
  have he := bounded_average_energy hr hB hb hs hC
  let a := (velocityLineAverage_memLp_two hr hb hs).toLp (velocityLineAverage r)
  have ha : ‖a‖^2 = ∫ x, ‖velocityLineAverage r x‖^2 := by
    rw [L2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [(velocityLineAverage_memLp_two hr hb hs).coeFn_toLp] with x hx
    rw [hx]
  change ‖a‖ ≤ _
  rw [← ha] at he
  nlinarith [sq_nonneg (‖a‖-1)]

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AverageFourierTail
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual velocity average satisfies the localized spectral estimate -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

theorem fourier_average_multiplier {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (k : FourierSpace) :
    𝓕 (velocityLineAverage r) k = ∫ v,
      complexVelocityMultiplier 1 (physicalFourierFrequency k) v * velocityFourier r (v,k) := by
  rw [fourier_velocityLineAverage hr]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    dsimp only
    rw [physicalFourierMultiplier]
    rfl)

theorem average_spectral_estimate {r : Velocity × FourierSpace → ℂ}
    (hr : Measurable r) (h₁ : Integrable r) (h₂ : MemLp r 2 volume) {R : ℝ}
    (hs : ∀ᵐ p ∂(volume : Measure (Velocity × FourierSpace)), R < ‖p.1‖ → r p = 0) :
    ∀ᵐ k ∂(volume : Measure FourierSpace),
      ‖𝓕 (velocityLineAverage r) k‖^2 ≤
        velocityMultiplierMass R 1 (physicalFourierFrequency k) *
          ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2 := by
  have hi := velocityFourier_integrable_sq hr h₁ h₂
  have hsupport := velocityFourier_support hs
  filter_upwards [hi.prod_left_ae] with k hk
  have hmem : MemLp (fun v => velocityFourier r (v,k)) 2
      (volume.restrict (Metric.closedBall (0 : Velocity) R)) := by
    apply (memLp_two_iff_integrable_sq_norm
      (((velocityFourier_measurable hr).comp measurable_prodMk_right).aestronglyMeasurable.restrict)).mpr
    exact hk.restrict
  have he : (∫ v in Metric.closedBall (0 : Velocity) R,
        complexVelocityMultiplier 1 (physicalFourierFrequency k) v * velocityFourier r (v,k)) =
      ∫ v, complexVelocityMultiplier 1 (physicalFourierFrequency k) v * velocityFourier r (v,k) := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupport] with v hv
    intro hnot
    have hR : R < ‖v‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hnot
    rw [hv hR k,mul_zero]
  rw [fourier_average_multiplier h₁,← he]
  apply (velocity_spectral_integral_bound R (physicalFourierFrequency k) hmem).trans
  apply mul_le_mul_of_nonneg_left _ (velocityMultiplierMass_nonneg _ _ _)
  exact setIntegral_le_integral hk (ae_of_all _ (fun v => sq_nonneg _))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform Fourier tails for the actual bounded velocity averages -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

attribute [local irreducible] velocityFourier velocityLineAverage physicalFourierFrequency

theorem average_fourier_tail {R ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (r : Velocity × FourierSpace → ℂ),
      Measurable r → Integrable r → MemLp r 2 volume →
      MemLp (velocityLineAverage r) 2 volume →
      (∀ᵐ p ∂(volume : Measure (Velocity × FourierSpace)), R < ‖p.1‖ → r p = 0) →
      (∫ k in {k : FourierSpace | (N:ℝ) ≤ ‖physicalFourierFrequency k‖},
        ‖𝓕 (velocityLineAverage r) k‖^2) ≤ ε * ∫ p, ‖r p‖^2 := by
  obtain ⟨N,hN,hbound⟩ := velocityMultiplierMass_high_frequency R hε
  refine ⟨N,hN,?_⟩
  intro r hr h₁ h₂ ha hs
  have hF := fourier_integral_memLp (velocityLineAverage_integrable h₁) ha
  have hFi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hpi := velocityFourier_integrable_sq hr h₁ h₂
  have hei : Integrable (fun k => ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2) :=
    hpi.integral_prod_right
  let S : Set FourierSpace := {k | (N:ℝ) ≤ ‖physicalFourierFrequency k‖}
  have hm : MeasurableSet S := by
    apply measurableSet_le measurable_const
    unfold physicalFourierFrequency
    fun_prop
  have hp : ∀ᵐ k ∂volume.restrict S,
      ‖𝓕 (velocityLineAverage r) k‖^2 ≤
        ε * ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2 := by
    filter_upwards [ae_restrict_of_ae (average_spectral_estimate hr h₁ h₂ hs),
      ae_restrict_mem hm] with k hk hks
    exact hk.trans (mul_le_mul_of_nonneg_right (hbound _ hks).le (integral_nonneg (fun v => sq_nonneg _)))
  calc
    _ ≤ ∫ k in S, ε * ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2 :=
      integral_mono_ae hFi.restrict (hei.const_mul ε).restrict hp
    _ ≤ ∫ k, ε * ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2 :=
      setIntegral_le_integral (hei.const_mul ε)
        (ae_of_all _ (fun k => mul_nonneg hε.le (integral_nonneg (fun v => sq_nonneg _))))
    _ = ε * ∫ p, ‖r p‖^2 := by
      rw [integral_const_mul,← integral_prod_symm _ hpi]
      change ε*(∫ p, ‖velocityFourier r p‖^2) = _
      rw [velocityFourier_energy hr h₁ h₂]

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedAverageCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform L2 Fourier tails on each bounded-source class -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

theorem bounded_average_uniform_tails (R B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Set FourierSpace, ∃ hS : MeasurableSet S, volume S < ⊤ ∧
      ∀ (r : Velocity × FourierSpace → ℂ) (hr : Integrable r), Measurable r →
      ∀ (hb : ∀ p, ‖r p‖ ≤ B) (hs : ∀ p, R < ‖p.1‖ → r p = 0),
      (∫ p, ‖r p‖) ≤ C →
      let a := (velocityLineAverage_memLp_two hr hb hs).toLp (velocityLineAverage r)
      ‖(𝓕 a : Lp ℂ 2 volume)-complexL2Cutoff S hS (𝓕 a)‖ ≤ δ := by
  let ε := δ^2/(B*C+1)
  have hden : 0 < B*C+1 := by positivity
  have hε : 0 < ε := by dsimp [ε] <;> positivity
  obtain ⟨N,-,hN⟩ := average_fourier_tail (R := R) hε
  let S : Set FourierSpace := {k | ‖physicalFourierFrequency k‖ < N}
  have hS : MeasurableSet S :=
    measurableSet_lt physicalFourierFrequency_continuous.norm.measurable measurable_const
  have hfS : volume S < ⊤ := lt_of_le_of_lt
    (measure_mono (fun k hk => show ‖physicalFourierFrequency k‖ ≤ (N:ℝ) from le_of_lt hk))
    (physicalFrequencyWindow_finite N)
  refine ⟨S,hS,hfS,?_⟩
  intro r hr hm hb hs hmass a
  have h₂ := integrable_bounded_memLp_two hr hb
  have ha := velocityLineAverage_memLp_two hr hb hs
  have he := hN r hm hr h₂ ha (Filter.Eventually.of_forall hs)
  have herr : ‖(𝓕 a : Lp ℂ 2 volume)-complexL2Cutoff S hS (𝓕 a)‖^2 ≤ δ^2 := by
    rw [complexL2Cutoff_error]
    calc
      _ = ∫ k in Sᶜ, ‖𝓕 (velocityLineAverage r) k‖^2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (fourier_L2_ae_eq_integral
          (velocityLineAverage_integrable hr) ha)] with k hk
        rw [hk]
      _ ≤ ε * ∫ p, ‖r p‖^2 := by simpa only [S,compl_ofPred,not_lt] using he
      _ ≤ ε*(B*C) := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        exact (bounded_integrable_square_le hr hb).trans
          (mul_le_mul_of_nonneg_left hmass hB)
      _ ≤ ε*(B*C+1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = δ^2 := by dsimp [ε]; field_simp
  nlinarith [norm_nonneg ((𝓕 a : Lp ℂ 2 volume)-complexL2Cutoff S hS (𝓕 a))]

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CommonBoundedAverageCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One subsequence for all bounded value truncations -/
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped Topology
namespace BoltzmannNonuniqueness.Published

theorem common_bounded_average_compactness (r : ℕ → ℕ → Velocity × FourierSpace → ℂ)
    (hm : ∀ m n, Measurable (r m n)) (hi : ∀ m n, Integrable (r m n))
    (R : ℝ) (B C : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hC : ∀ m, 0 ≤ C m)
    (hb : ∀ m n p, ‖r m n p‖ ≤ B m)
    (hs : ∀ m n p, R < ‖p.1‖ → r m n p = 0)
    (hbound : ∀ m n, (∫ p, ‖r m n p‖) ≤ C m) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Lp ℂ 2 (volume : Measure FourierSpace)), StrictMono φ ∧
      ∀ m (K : Set FourierSpace), volume K < ⊤ →
        Tendsto (fun n => ‖complexL2Restriction K
          (boundedAverageL2 (r m (φ n)) (hi m (φ n)) (hb m (φ n)) (hs m (φ n))-g m)‖)
          atTop (𝓝 0) := by
  let a m n := boundedAverageL2 (r m n) (hi m n) (hb m n) (hs m n)
  let u m n : Lp ℂ 2 (volume : Measure FourierSpace) := 𝓕 (a m n)
  let D m := volume.real (Metric.closedBall (0 : Velocity) R)*B m*C m+1
  have ha m n : ‖a m n‖ ≤ D m :=
    bounded_average_L2_norm (hi m n) (hB m) (hb m n) (hs m n) (hbound m n)
  have hu m n : ‖u m n‖ ≤ D m := by simpa only [u,Lp.norm_fourier_eq] using ha m n
  obtain ⟨φ,g,hφ,hg⟩ := exists_common_weak_complex_L2_subsequence u D hu
  refine ⟨φ,fun m => 𝓕⁻ (g m),hφ,?_⟩
  intro m K hK
  have hD : 0 ≤ D m := (norm_nonneg (u m 0)).trans (hu m 0)
  have ht : ∀ ε : ℝ, 0 < ε → ∃ S : Set FourierSpace, ∃ hS : MeasurableSet S,
      volume S < ⊤ ∧ ∀ n, ‖u m (φ n)-complexL2Cutoff S hS (u m (φ n))‖ ≤ ε := by
    intro ε hε
    obtain ⟨S,hS,hfinite,h⟩ := bounded_average_uniform_tails R (B m) (C m) (hB m) (hC m) hε
    exact ⟨S,hS,hfinite,fun n =>
      h (r m (φ n)) (hi m (φ n)) (hm m (φ n)) (hb m (φ n)) (hs m (φ n)) (hbound m (φ n))⟩
  have h := inverseFourier_local_strong_of_weak_and_tails hD (fun n => hu m (φ n))
    (hg m).1 (hg m).2 ht K hK
  simpa only [u,fourierInv_fourier_eq] using h

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SpacetimeAverageLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Returning the complex averaged limit to real spacetime -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem spacetime_average_limit (r : ℕ → KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (hi : ∀ n, Integrable (fourierSource (r n) ψ))
    (q : Lp ℂ 1 (volume : Measure FourierSpace))
    (hc : ∀ K : Set FourierSpace, volume K < ⊤ →
      Tendsto (fun n => eLpNorm (velocityLineAverage (fourierSource (r n) ψ)-
        (q : FourierSpace → ℂ)) 1 (volume.restrict K)) atTop (𝓝 0)) :
    LocalL1Converges (fun n => resolventAverage (r n) ψ)
      (fun z => (q (spacetimeHilbertEquiv z)).re) := by
  have hq : Integrable (fun z => q (spacetimeHilbertEquiv z)) :=
    spacetimeHilbert_measurePreserving.integrable_comp_of_integrable (L1.integrable_coeFn q)
  refine ⟨hq.re.locallyIntegrable,fun K hK => ?_⟩
  let S := spacetimeHilbertEquiv '' K
  have hS : volume S < ⊤ := by
    have he := spacetimeHilbert_measurePreserving.measure_preimage_emb
      spacetimeHilbertEquiv.measurableEmbedding S
    rw [show spacetimeHilbertEquiv ⁻¹' S = K from
      preimage_image_eq _ spacetimeHilbertEquiv.injective] at he
    exact he ▸ hK.measure_lt_top
  have he n : eLpNorm (fun z => velocityLineAverage (fourierSource (r n) ψ)
      (spacetimeHilbertEquiv z)-q (spacetimeHilbertEquiv z)) 1 (volume.restrict K) =
      eLpNorm (velocityLineAverage (fourierSource (r n) ψ)-(q : FourierSpace → ℂ))
        1 (volume.restrict S) :=
    by
      simpa only [Function.comp_def,Pi.sub_apply,S] using
        eLpNorm_comp_equiv_restrict spacetimeHilbertEquiv spacetimeHilbert_measurePreserving
          (velocityLineAverage (fourierSource (r n) ψ)-(q : FourierSpace → ℂ)) K
  have hb n : eLpNorm (fun z => resolventAverage (r n) ψ z-(q (spacetimeHilbertEquiv z)).re)
      1 (volume.restrict K) ≤
      eLpNorm (velocityLineAverage (fourierSource (r n) ψ)-(q : FourierSpace → ℂ))
        1 (volume.restrict S) := by
    rw [← he n]
    have hav := spacetimeHilbert_measurePreserving.integrable_comp_of_integrable
      (velocityLineAverage_integrable (hi n))
    have hm : AEStronglyMeasurable (fun z => (velocityLineAverage (fourierSource (r n) ψ)
        (spacetimeHilbertEquiv z)-q (spacetimeHilbertEquiv z)).re) (volume.restrict K) :=
      (hav.sub hq).aestronglyMeasurable.re.restrict
    apply eLpNorm_mono
    intro z
    rw [fourierSource_average]
    simpa only [Complex.sub_re,Complex.ofReal_re,Real.norm_eq_abs] using
      Complex.abs_re_le_norm ((resolventAverage (r n) ψ z : ℂ)-q (spacetimeHilbertEquiv z))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hc S hS)
    (fun _ => bot_le) hb

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityAverageRepresentatives
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Almost-everywhere representatives do not change the velocity average -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

theorem velocityLineAverage_congr_ae {r q : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (hq : Integrable q) (he : r =ᵐ[volume] q) :
    velocityLineAverage r =ᵐ[volume] velocityLineAverage q := by
  have hz : eLpNorm (r-q) 1 volume = 0 := by
    have hzero : r-q =ᵐ[volume] 0 := by
      filter_upwards [he] with p hp
      simp only [Pi.sub_apply,Pi.zero_apply,hp,sub_self]
    rw [eLpNorm_congr_ae hzero,eLpNorm_zero]
  have hb := velocityLineAverage_difference_le hr hq
  rw [hz] at hb
  have ha := (eLpNorm_eq_zero_iff ((velocityLineAverage_integrable hr).1.sub
      (velocityLineAverage_integrable hq).1) (by norm_num : (1 : ℝ≥0∞) ≠ 0)).mp
    (le_antisymm hb bot_le)
  filter_upwards [ha] with x hx
  exact sub_eq_zero.mp hx

theorem measurable_velocity_representative (r : ℕ → KineticPhase → ℝ)
    (hui : UniformIntegrable r 1 volume) (R : ℝ)
    (hs : ∀ n, ∀ᵐ z ∂volume, R < ‖z.2‖ → r n z = 0) :
    ∃ u : ℕ → KineticPhase → ℝ, (∀ n, Measurable (u n)) ∧
      (∀ n, u n =ᵐ[volume] r n) ∧
      (∀ n z, R < ‖z.2‖ → u n z = 0) := by
  let u n := {z : KineticPhase | ‖z.2‖ ≤ R}.indicator ((hui.aestronglyMeasurable n).mk (r n))
  have hS : MeasurableSet {z : KineticPhase | ‖z.2‖ ≤ R} := by measurability
  refine ⟨u,fun n => (hui.aestronglyMeasurable n).stronglyMeasurable_mk.measurable.indicator hS,?_,?_⟩
  · intro n
    filter_upwards [(hui.aestronglyMeasurable n).ae_eq_mk,hs n] with z hz hs'
    by_cases h : ‖z.2‖ ≤ R
    · simpa [u,h] using hz.symm
    · rw [show u n z = 0 by simp [u,h]]
      exact (hs' (lt_of_not_ge h)).symm
  · intro n z hz
    simp [u,not_le.mpr hz]

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformAverageCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniformly integrable sources have locally compact velocity averages -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

theorem uniform_average_compactness (r : ℕ → Velocity × FourierSpace → ℂ)
    (hm : ∀ n, Measurable (r n)) (hui : UniformIntegrable r 1 volume)
    (R : ℝ) (hs : ∀ n p, R < ‖p.1‖ → r n p = 0) :
    ∃ (φ : ℕ → ℕ) (g : Lp ℂ 1 (volume : Measure FourierSpace)), StrictMono φ ∧
      ∀ K : Set FourierSpace, volume K < ⊤ →
        Tendsto (fun n => eLpNorm (velocityLineAverage (r (φ n))-(g : FourierSpace → ℂ))
          1 (volume.restrict K)) atTop (𝓝 0) := by
  classical
  have hi n : Integrable (r n) := memLp_one_iff_integrable.mp (hui.memLp n)
  obtain ⟨C,hC⟩ := hui.2
  have hmass n : (∫ p, ‖r n p‖) ≤ (C : ℝ) := by
    have h := hC n
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n)] at h
    exact (ENNReal.ofReal_le_ofReal_iff C.coe_nonneg).mp (by simpa only [ENNReal.ofReal_coe_nnreal] using h)
  have ht m := uniform_value_truncation r hm hui
    (ENNReal.ofReal_pos.mpr (truncationError_pos m))
  choose B u hum hub hus hud hue using ht
  have hui' m n : Integrable (u m n) :=
    (hi n).norm.mono' (hum m n).aestronglyMeasurable (ae_of_all _ (hud m n))
  have hus' m n p (hp : R < ‖p.1‖) : u m n p = 0 := hus m n p (hs n p hp)
  have humass m n : (∫ p, ‖u m n p‖) ≤ (C : ℝ) :=
    (integral_mono (hui' m n).norm (hi n).norm (hud m n)).trans (hmass n)
  obtain ⟨φ,g,hφ,hg⟩ := common_bounded_average_compactness u hum hui' R
    (fun m => B m) (fun _ => C) (fun m => (B m).coe_nonneg) (fun _ => C.coe_nonneg)
    hub hus' humass
  have hlocal m (K : Set FourierSpace) (hK : volume K < ⊤) :
      Tendsto (fun n => eLpNorm (velocityLineAverage (u m (φ n))-(g m : FourierSpace → ℂ))
        1 (volume.restrict K)) atTop (𝓝 0) := by
    have h := localL2_L1_tendsto K hK (hg m K hK)
    have he n : eLpNorm (boundedAverageL2 (u m (φ n)) (hui' m (φ n))
        (hub m (φ n)) (hus' m (φ n))-g m : Lp ℂ 2 volume) 1 (volume.restrict K) =
        eLpNorm (velocityLineAverage (u m (φ n))-(g m : FourierSpace → ℂ)) 1 (volume.restrict K) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub
        (boundedAverageL2 (u m (φ n)) (hui' m (φ n)) (hub m (φ n)) (hus' m (φ n))) (g m)),
        ae_restrict_of_ae (MemLp.coeFn_toLp (velocityLineAverage_memLp_two
          (hui' m (φ n)) (hub m (φ n)) (hus' m (φ n))))] with x hx ha
      simp only [Pi.sub_apply] at hx ⊢
      rw [hx]
      change (boundedAverageL2 (u m (φ n)) (hui' m (φ n)) (hub m (φ n)) (hus' m (φ n))) x = velocityLineAverage (u m (φ n)) x at ha
      rw [ha]
    simpa only [he] using h
  have hbound m n : eLpNorm (velocityLineAverage (u m n)) 1 volume ≤ (C : ℝ≥0∞) := by
    apply (velocityLineAverage_eLpNorm_le (hui' m n)).trans
    exact (eLpNorm_mono (hud m n)).trans (hC n)
  have hgi m : Integrable (g m : FourierSpace → ℂ) := by
    have h := localL1_global_bound (Lp.aestronglyMeasurable (g m)) (C : ℝ≥0∞)
      (fun n => hbound m (φ n)) (hlocal m)
      (fun n => (velocityLineAverage_integrable (hui' m (φ n))).1)
    refine ⟨Lp.aestronglyMeasurable (g m),?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact h.trans_lt ENNReal.coe_lt_top
  have herr m n : eLpNorm (velocityLineAverage (r (φ n))-velocityLineAverage (u m (φ n)))
      1 volume ≤ ENNReal.ofReal (truncationError m) :=
    (velocityLineAverage_difference_le (hi (φ n)) (hui' m (φ n))).trans (hue m (φ n))
  obtain ⟨q,hq⟩ := localL1_approximation_limit (fun n => velocityLineAverage (r (φ n)))
    (fun m n => velocityLineAverage (u m (φ n))) (fun m => (g m : FourierSpace → ℂ))
    hgi truncationError (fun m => (truncationError_pos m).le) truncationError_tendsto herr hlocal
    (fun n => (velocityLineAverage_integrable (hi (φ n))).1)
    (fun m n => (velocityLineAverage_integrable (hui' m (φ n))).1)
  exact ⟨φ,q,hφ,hq⟩

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_VelocityAveraging
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The needed Golse–Lions–Perthame–Sentis compactness specialization

This proves the exact input from Proposition 3 (pp. 115–116) and the evolution
extension, Remark (2) (p. 119), JFA 76 (1988). The velocity measure is Lebesgue
measure on a ball. Bounded value truncations have uniformly small Fourier tails;
one common subsequence converges locally in L2. Uniform L1 approximation then
constructs the global L1 limit and yields local L1 convergence for the original
sources. No spatial tightness or extra compactness hypothesis is imposed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem glps1988Proposition3_q80_oai : GLPS1988Proposition3 := by
  intro r R _ hs hui ψ hψ hsupport
  obtain ⟨u,hum,hue,hus⟩ := measurable_velocity_representative r hui R hs
  have huiu : UniformIntegrable u 1 volume := hui.ae_eq (fun n => (hue n).symm)
  have huif := fourierSource_uniformIntegrable u hum huiu ψ hψ.continuous hsupport
  have hui' n : Integrable (fourierSource (u n) ψ) :=
    memLp_one_iff_integrable.mp (huif.memLp n)
  have hs' n (p : Velocity × FourierSpace) (hp : R < ‖p.1‖) : fourierSource (u n) ψ p = 0 := by
    simp only [fourierSource,hus n (p.2.ofLp,p.1) hp,mul_zero,Complex.ofReal_zero]
  obtain ⟨φ,g,hφ,hg⟩ := uniform_average_compactness (fun n => fourierSource (u n) ψ)
    (fun n => fourierSource_measurable (hum n) hψ.continuous.measurable) huif R hs'
  have he n : fourierSource (r n) ψ =ᵐ[volume] fourierSource (u n) ψ :=
    fourierSource_congr_ae ψ (hue n).symm
  have hri n : Integrable (fourierSource (r n) ψ) := (hui' n).congr (he n).symm
  refine ⟨φ,fun z => (g (spacetimeHilbertEquiv z)).re,hφ,?_⟩
  apply spacetime_average_limit (fun n => r (φ n)) ψ (fun n => hri (φ n)) g
  intro K hK
  have heq n : eLpNorm (velocityLineAverage (fourierSource (r (φ n)) ψ)-(g : FourierSpace → ℂ))
      1 (volume.restrict K) =
      eLpNorm (velocityLineAverage (fourierSource (u (φ n)) ψ)-(g : FourierSpace → ℂ))
      1 (volume.restrict K) := by
    apply eLpNorm_congr_ae
    exact ae_restrict_of_ae ((velocityLineAverage_congr_ae (hri (φ n)) (hui' (φ n))
      (he (φ n))).sub ae_eq_rfl)
  simpa only [heq] using hg K hK

end BoltzmannNonuniqueness.Published

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.Published.glps1988Proposition3_q80_oai := @OAI.BoltzmannNonuniqueness.Published.glps1988Proposition3_q80_oai
