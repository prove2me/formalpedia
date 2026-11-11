-- Prove2me | solution 1 for OAI.Problem367.free_ising_factor_iff_threshold
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:59.322842+00:00
-- url     : https://prove2.me/submissions/537b8265-3780-49d9-99c5-df5a34c2ce9d

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI003
import Definitions.Def_Q243FI004
import Theorems.Thm_OAI_Problem367_IsingObservationFactor_actual_variance_analysis
import Theorems.Thm_OAI_Problem367_free_ising_factor_below_threshold_of_actual_variance_identity

section
-- module Solutions.Q243_FreeIsing.UnifIntegrableCompat
attribute [-instance] _root_.OAI.closedSubmoduleNormedAddCommGroup _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv
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

end UnifIntegrable

theorem unifIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UnifIntegrable (fun _ : ι => g) p μ :=
  ⟨MeasureTheory.unifIntegrable_const hp hp_ne_top hg, fun _ => hg.1⟩

theorem tendsto_Lp_finite_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  MeasureTheory.tendsto_Lp_finite_of_tendsto_ae hp hp' hf hg hui.1 hfg

/-! ### `UniformIntegrable` -/

/-! ### `UnifTight` -/

end OAI

end UnifIntegrableCompat
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteCoordinateFiltration
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem367

theorem coordinateFiltration_iSup
    {ι : Type*} {X : ι → Type*} [m : ∀ i, MeasurableSpace (X i)]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n) :
    (⨆ n, coordinateFiltration (X := X) s hs n) = MeasurableSpace.pi := by
  apply le_antisymm
  · exact iSup_le fun n => (coordinateFiltration s hs).le n
  · change (⨆ i, (m i).comap (fun x : ∀ i, X i => x i)) ≤ _
    refine iSup_le fun i => ?_
    obtain ⟨n, hn⟩ := hex i
    exact le_iSup_of_le n (le_iSup_of_le i (le_iSup_of_le hn le_rfl))

theorem tendsto_ae_coordinate_condExp
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ} (hf : Measurable f) (hfi : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => μ[f | cylinderEvents (s n)] x) atTop (𝓝 (f x)) := by
  apply hfi.tendsto_ae_condExp (ℱ := coordinateFiltration s hs)
  rw [coordinateFiltration_iSup s hs hex]
  exact hf.stronglyMeasurable

theorem tendsto_Lp_coordinate_condExp_of_bounded
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ} (hf : Measurable f)
    {R : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ R)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (μ[f | cylinderEvents (s n)] - f) p μ) atTop (𝓝 0) := by
  have hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖R‖ :=
    hbound.mono fun x hx => hx.trans (by exact le_abs_self R)
  have hmem : MemLp f p μ := (memLp_const R).mono hf.aestronglyMeasurable hb
  have hfi : Integrable f μ := hmem.integrable hp
  have hcb (n : ℕ) : ∀ᵐ x ∂μ, ‖μ[f | cylinderEvents (s n)] x‖ ≤ ‖R‖ :=
    ae_bdd_norm_condExp_of_ae_bdd_norm hb
  have hui : UnifIntegrable (fun n => μ[f | cylinderEvents (s n)]) p μ := by
    apply OAI.UnifIntegrable.of_enn
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ :=
      OAI.UnifIntegrable.enn_spec
        (unifIntegrable_const (ι := ℕ) (μ := μ) hp hpt (memLp_const R)) ε hε
    refine ⟨δ, hδ, fun index region hμregion => ?_⟩
    exact (eLpNorm_mono_ae
      ((hcb index).filter_mono ae_restrict_le)).trans
      (hδε index region hμregion)
    exact fun n => (stronglyMeasurable_condExp.mono cylinderEvents_le_pi).aestronglyMeasurable
  exact tendsto_Lp_finite_of_tendsto_ae hp hpt
    (fun n => (stronglyMeasurable_condExp.mono cylinderEvents_le_pi).aestronglyMeasurable)
    hmem hui (tendsto_ae_coordinate_condExp μ s hs hex hf hfi)

theorem tendsto_Lp_coordinate_condExp
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) (hmem : MemLp f p μ) :
    Tendsto (fun n => eLpNorm (μ[f | cylinderEvents (s n)] - f) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδ : ε / 3 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε.ne', by norm_num⟩
  obtain ⟨g, hfg, hgm⟩ := hmem.exists_simpleFunc_eLpNorm_sub_lt hpt hδ
  obtain ⟨R, hR⟩ := (g.finite_range.image (fun y : ℝ => ‖y‖)).bddAbove
  have hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ R := Filter.Eventually.of_forall fun x =>
    hR ⟨g x, ⟨x, rfl⟩, rfl⟩
  have hlim := tendsto_Lp_coordinate_condExp_of_bounded μ s hs hex g.measurable hgb hp hpt
  have hev := ENNReal.tendsto_nhds_zero.mp hlim (ε / 3) (pos_iff_ne_zero.mpr hδ)
  filter_upwards [hev] with n hn
  have hcontract : eLpNorm (μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) p μ ≤
      eLpNorm (f - ⇑g) p μ := by
    rw [← eLpNorm_congr_ae (condExp_sub (hmem.integrable hp) (hgm.integrable hp) (cylinderEvents (s n)))]
    exact eLpNorm_condExp_le_eLpNorm _ hp
  have hdecomp : μ[f | cylinderEvents (s n)] - f =
      (μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) +
      (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)] - ⇑g) + (⇑g - f) := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hcf : AEStronglyMeasurable (μ[f | cylinderEvents (s n)]) μ := integrable_condExp.aestronglyMeasurable
  have hcg : AEStronglyMeasurable (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) μ := integrable_condExp.aestronglyMeasurable
  have hgm' : AEStronglyMeasurable (⇑g) μ := g.aestronglyMeasurable
  have hfm : AEStronglyMeasurable f μ := hmem.aestronglyMeasurable
  calc
    eLpNorm (μ[f | cylinderEvents (s n)] - f) p μ
      = eLpNorm ((μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) +
          (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)] - ⇑g) + (⇑g - f)) p μ := by rw [hdecomp]
    _ ≤ (eLpNorm (μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) p μ +
          eLpNorm (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)] - ⇑g) p μ) + eLpNorm (⇑g - f) p μ := by
      exact (eLpNorm_add_le (hf := (hcf.sub hcg).add (hcg.sub hgm')) (hg := hgm'.sub hfm) hp).trans (add_le_add (eLpNorm_add_le (hf := hcf.sub hcg) (hg := hcg.sub hgm') hp) le_rfl)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
      apply add_le_add
      · exact add_le_add (hcontract.trans hfg.le) hn
      · rw [eLpNorm_sub_comm]
        exact hfg.le
    _ = ε := ENNReal.add_thirds ε

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteCoordinateRepresentation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem367

theorem cylinderEvents_eq_comap_restrict
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] (D : Set ι) :
    cylinderEvents (X := X) D = MeasurableSpace.pi.comap D.domRestrict := by
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  simp only [cylinderEvents, iSup_subtype]
  rfl

theorem exists_coordinate_condExp_rep
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) (D : Set ι) (f : (∀ i, X i) → ℝ) :
    ∃ g : (∀ i : D, X i) → ℝ, Measurable g ∧
      μ[f | cylinderEvents D] = g ∘ D.domRestrict := by
  have hm := stronglyMeasurable_condExp (μ := μ) (f := f) (m := cylinderEvents D)
  rw [cylinderEvents_eq_comap_restrict] at hm
  obtain ⟨g, hg, h⟩ := hm.exists_eq_measurable_comp
  exact ⟨g, hg.measurable, by simpa only [cylinderEvents_eq_comap_restrict] using h⟩

theorem exists_finite_coordinate_Lp_approx
    {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    {f : (∀ i, X i) → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) (hf : MemLp f p μ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (s : Finset ι) (g : (∀ i : s, X i) → ℝ),
      Measurable g ∧ MemLp (g ∘ s.restrict) p μ ∧
      (∫ x, g (s.restrict x) ∂μ) = ∫ x, f x ∂μ ∧
      eLpNorm (f - g ∘ s.restrict) p μ < ε := by
  let : Encodable ι := Encodable.ofCountable ι
  let s : ℕ → Finset ι := fun n =>
    ((Set.finite_Iic n).preimage Encodable.encode_injective.injOn).toFinset
  have hs : Monotone (fun n => (s n : Set ι)) := by
    intro n m hnm i hi
    simp only [s, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_Iic] at hi ⊢
    exact hi.trans hnm
  have hex : ∀ i : ι, ∃ n, i ∈ (s n : Set ι) := by
    intro i
    refine ⟨Encodable.encode i, ?_⟩
    simp [s]
  have hlim := tendsto_Lp_coordinate_condExp μ (fun n => (s n : Set ι)) hs hex hp hpt hf
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hε)).exists
  obtain ⟨g, hg, hrep⟩ := exists_coordinate_condExp_rep μ (s n : Set ι) f
  refine ⟨s n, g, hg, ?_, ?_, ?_⟩
  · change MemLp (g ∘ (s n : Set ι).domRestrict) p μ
    rw [← hrep]
    exact MemLp.condExp hp hf
  · change (∫ x, (g ∘ (s n : Set ι).domRestrict) x ∂μ) = _
    rw [← hrep]
    exact integral_condExp cylinderEvents_le_pi
  change eLpNorm (f - g ∘ (s n : Set ι).domRestrict) p μ < ε
  rw [← hrep, eLpNorm_sub_comm]
  exact hn

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_KoopmanInvolutions
attribute [-instance] _root_.OAI.Problem367.CopyDifference.rangeClosure_completeSpace _root_.OAI.Problem367.SpectralClosure.rangeClosure_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem koopmanAverage_selfAdjoint {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    IsSelfAdjoint (koopmanAverage τ hτ) := by
  unfold koopmanAverage
  refine (IsSelfAdjoint.all _).smul ?_
  exact isSelfAdjoint_sum (R := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) Finset.univ fun index _ =>
    koopmanL2_selfAdjoint (τ index) (hτ index) (hinv index)

section Centered

variable [IsFiniteMeasure μ]

theorem centeredKoopmanAverage_selfAdjoint {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    IsSelfAdjoint (centeredKoopmanAverage τ hτ hinv) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact (koopmanAverage_selfAdjoint τ hτ hinv).isSymmetric.restrict_invariant
    (koopmanAverage_preserves_centered τ hτ hinv)

end Centered

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CenteredLocalDensity
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanEquiv_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanIsometry_apply_coe _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367

theorem dense_centered_finite_coordinate
    {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ] :
    Dense {f : centeredL2 μ | ∃ (s : Finset ι) (g : (∀ i : s, X i) → ℝ),
      Measurable g ∧ (fun x => (f : Lp ℝ 2 μ) x) =ᵐ[μ] g ∘ s.restrict} := by
  apply Metric.dense_iff.mpr
  intro f ε hε
  obtain ⟨s, g, hgm, hgLp, hint, happrox⟩ :=
    exists_finite_coordinate_Lp_approx μ (by norm_num : 1 ≤ (2 : ENNReal))
      (by norm_num : (2 : ENNReal) ≠ ⊤) (Lp.memLp (f : Lp ℝ 2 μ))
      (ENNReal.ofReal_pos.mpr hε)
  let gLp : Lp ℝ 2 μ := hgLp.toLp (g ∘ s.restrict)
  have hcenter : gLp ∈ centeredL2 μ := by
    rw [mem_centeredL2_iff]
    calc
      (∫ x, gLp x ∂μ) = ∫ x, g (s.restrict x) ∂μ :=
        integral_congr_ae hgLp.coeFn_toLp
      _ = ∫ x, (f : Lp ℝ 2 μ) x ∂μ := hint
      _ = 0 := (mem_centeredL2_iff _).mp f.property
  refine ⟨⟨gLp, hcenter⟩, ?_, s, g, hgm, hgLp.coeFn_toLp⟩
  change dist gLp (f : Lp ℝ 2 μ) < ε
  rw [dist_comm, Lp.dist_def]
  apply ENNReal.toReal_lt_of_lt_ofReal
  rw [eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hgLp.coeFn_toLp)]
  exact happrox

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Regularity
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367

theorem treeStep_length {d : ℕ} (v : TreeVertex d) (c : Fin d) :
    (treeStep v c).1.length =
      if v.1.getLast? = some c then v.1.length - 1 else v.1.length + 1 := by
  unfold treeStep
  split_ifs <;> simp

theorem sum_treeNeighborFinset_radial {d : ℕ} (v : TreeVertex d) (F : ℕ → ℝ) :
    ∑ w ∈ treeNeighborFinset v, F w.1.length =
      if v.1.length = 0 then (d : ℝ) * F 1
      else F (v.1.length - 1) + ((d : ℝ) - 1) * F (v.1.length + 1) := by
  classical
  rw [treeNeighborFinset, Finset.sum_image (treeStep_injective v).injOn]
  by_cases hv : v.1.length = 0
  · have hnil := List.length_eq_zero_iff.mp hv
    simp [treeStep_length, hnil]
  · have hne : v.1 ≠ [] := by
      intro hnil
      exact hv (List.length_eq_zero_iff.mpr hnil)
    let c := v.1.getLast hne
    have hc : v.1.getLast? = some c := List.getLast?_eq_some_getLast hne
    have hd : 1 ≤ d := by have := c.isLt; omega
    rw [ite_eq_right hv, ← Finset.add_sum_erase Finset.univ
      (fun a : Fin d => F (treeStep v a).1.length) (Finset.mem_univ c)]
    simp only [treeStep_length, hc, Option.some.injEq]
    congr 1
    calc
      ∑ a ∈ Finset.univ.erase c,
          F (if c = a then v.1.length - 1 else v.1.length + 1) =
          ∑ _a ∈ Finset.univ.erase c, F (v.1.length + 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [ite_eq_right (Ne.symm (Finset.mem_erase.mp ha).1)]
      _ = ((d : ℝ) - 1) * F (v.1.length + 1) := by
        simp [Nat.cast_sub hd]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialWalk
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace RadialWalk

variable {V : Type*} {d : ℕ}

theorem average_mono (step : V → Fin d → V) {f g : V → ℝ}
    (h : ∀ v, f v ≤ g v) : ∀ v, average step f v ≤ average step g v := by
  intro v
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun c _ => h (step v c)))
    (Nat.cast_nonneg d)

theorem average_mul (step : V → Fin d → V) (a : ℝ) (f : V → ℝ) (v : V) :
    average step (fun w => a * f w) v = a * average step f v := by
  unfold average
  rw [← Finset.mul_sum]
  ring

theorem iterate_bound (step : V → Fin d → V) (q : V → ℝ)
    {rho : ℝ} (hrho : 0 ≤ rho) (hq : ∀ v, average step q v ≤ rho * q v)
    (n : ℕ) : ∀ v, ((average step)^[n]) q v ≤ rho ^ n * q v := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [Function.iterate_succ_apply']
    calc
      average step (((average step)^[n]) q) v ≤
          average step (fun w => rho ^ n * q w) v := average_mono step ih v
      _ = rho ^ n * average step q v := average_mul step _ _ _
      _ ≤ rho ^ n * (rho * q v) := mul_le_mul_of_nonneg_left (hq v) (pow_nonneg hrho n)
      _ = rho ^ (n + 1) * q v := by rw [pow_succ]; ring

theorem abs_average_le (step : V → Fin d → V) (f : V → ℝ) (v : V) :
    |average step f v| ≤ average step (fun w => |f w|) v := by
  unfold average
  rw [abs_div, show |(d : ℝ)| = d from abs_of_nonneg (Nat.cast_nonneg d)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg d)

theorem abs_iterate_average_le (step : V → Fin d → V) (f : V → ℝ) (n : ℕ) :
    ∀ v, |((average step)^[n]) f v| ≤
      ((average step)^[n]) (fun w => |f w|) v := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (abs_average_le _ _ _).trans (average_mono step ih v)

theorem iterate_average_mono (step : V → Fin d → V) {f g : V → ℝ}
    (h : ∀ v, f v ≤ g v) (n : ℕ) :
    ∀ v, ((average step)^[n]) f v ≤ ((average step)^[n]) g v := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact average_mono step ih

theorem iterate_average_mul (step : V → Fin d → V) (a : ℝ) (f : V → ℝ) (n : ℕ) :
    ((average step)^[n]) (fun w => a * f w) =
      fun v => a * ((average step)^[n]) f v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext v
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    exact average_mul step _ _ _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem inner_vectorAverage (step : V → Fin d → V) (x : H) (f : V → H) (v : V) :
    inner ℝ x (vectorAverage step f v) = average step (fun w => inner ℝ x (f w)) v := by
  simp only [vectorAverage, inner_smul_right, inner_sum, average]
  ring

theorem inner_iterate_vectorAverage (step : V → Fin d → V) (x : H) (f : V → H)
    (n : ℕ) :
    (fun v => inner ℝ x (((vectorAverage step)^[n]) f v)) =
      ((average step)^[n]) (fun v => inner ℝ x (f v)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext v
    rw [Function.iterate_succ_apply', inner_vectorAverage, ih,
      Function.iterate_succ_apply']

theorem inner_iterate_bound (step : V → Fin d → V) (x : H) (f : V → H)
    (q : V → ℝ) {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (hq : ∀ v, average step q v ≤ rho * q v)
    (hf : ∀ v, |inner ℝ x (f v)| ≤ C * q v)
    (n : ℕ) (v : V) :
    |inner ℝ x (((vectorAverage step)^[n]) f v)| ≤ C * rho ^ n * q v := by
  have hinner := congrFun (inner_iterate_vectorAverage step x f n) v
  rw [hinner]
  calc
    |((average step)^[n]) (fun w => inner ℝ x (f w)) v| ≤
        ((average step)^[n]) (fun w => |inner ℝ x (f w)|) v :=
      abs_iterate_average_le step _ n v
    _ ≤ ((average step)^[n]) (fun w => C * q w) v := iterate_average_mono step hf n v
    _ = C * ((average step)^[n]) q v := congrFun (iterate_average_mul step C q n) v
    _ ≤ C * (rho ^ n * q v) := mul_le_mul_of_nonneg_left (iterate_bound step q hrho hq n v) hC
    _ = C * rho ^ n * q v := by ring

theorem rate_nonneg (d : ℕ) : 0 ≤ rate d := by
  exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Nat.cast_nonneg d)

theorem root_bound {d : ℕ} (hd : 3 ≤ d) : weight d 1 ≤ rate d * weight d 0 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  simp only [weight, rate, pow_one, pow_zero, mul_one]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hs (by positivity : (0 : ℝ) < d)).2
  nlinarith

theorem recurrence {d : ℕ} (hd : 3 ≤ d) (n : ℕ) :
    (weight d n + ((d : ℝ) - 1) * weight d (n + 2)) / d =
      rate d * weight d (n + 1) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hs : Real.sqrt ((d : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hs2 := Real.sq_sqrt hb.le
  unfold weight rate
  simp only [pow_succ]
  field_simp
  nlinarith

theorem average_treeWeight_le {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d) :
    average treeStep (treeWeight d) v ≤ rate d * treeWeight d v := by
  classical
  have hsum := sum_treeNeighborFinset_radial v (weight d)
  rw [treeNeighborFinset, Finset.sum_image (treeStep_injective v).injOn] at hsum
  unfold average treeWeight
  rw [hsum]
  by_cases hv : v.1.length = 0
  · rw [ite_eq_left hv, hv]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hcancel : (d : ℝ) * weight d 1 / d = weight d 1 := by field_simp
    rw [hcancel]
    exact root_bound hd
  · rw [ite_eq_right hv]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hv
    rw [hn]
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using (recurrence hd n).le

theorem covariance_walk_bound {d : ℕ} (hd : 3 ≤ d) (f : TreeVertex d → H)
    (o : TreeVertex d) (ho : o.1.length = 0) {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ (f o) (f v)| ≤ C * treeWeight d v) (n : ℕ) :
    |inner ℝ (f o) (((vectorAverage treeStep)^[n]) f o)| ≤ C * rate d ^ n := by
  simpa only [treeWeight, ho, weight, pow_zero, mul_one] using
    inner_iterate_bound treeStep (f o) f (treeWeight d) hC (rate_nonneg d)
      (average_treeWeight_le hd) hcov n o

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialRepresentation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367
namespace RadialWalk

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem wordOperator_step (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (v : TreeVertex d) (c : Fin d) :
    wordOperator S (treeStep v c) = wordOperator S v * S c := by
  rcases (treeStep_eq_iff v (treeStep v c) c).mp rfl with h | h
  · simp [wordOperator, h, List.map_append, List.prod_append]
  · have hv : wordOperator S v = wordOperator S (treeStep v c) * S c := by
      simp [wordOperator, h, List.map_append, List.prod_append]
    rw [hv, mul_assoc, hS c, mul_one]

theorem operatorAverage_apply (S : Fin d → H →L[ℝ] H) (x : H) :
    operatorAverage S x = (d : ℝ)⁻¹ • ∑ c, S c x := by
  simp [operatorAverage]

theorem vectorAverage_wordOperator (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (x : H) (v : TreeVertex d) :
    vectorAverage treeStep (fun w => wordOperator S w x) v =
      wordOperator S v (operatorAverage S x) := by
  simp only [vectorAverage, wordOperator_step S hS, mul_apply_eq_comp,
    operatorAverage_apply, map_smul, map_sum]

theorem iterate_vectorAverage_wordOperator (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (x : H) (n : ℕ) :
    ((vectorAverage treeStep)^[n]) (fun w => wordOperator S w x) =
      fun w => wordOperator S w ((operatorAverage S ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext v
    rw [Function.iterate_succ_apply', ih, vectorAverage_wordOperator S hS]
    rw [pow_succ']
    rfl

theorem matrix_coefficient_power_bound (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (hd : 3 ≤ d) (x : H)
    {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ x (wordOperator S v x)| ≤ C * treeWeight d v)
    (n : ℕ) :
    |inner ℝ x ((operatorAverage S ^ n) x)| ≤ C * rate d ^ n := by
  let o : TreeVertex d := ⟨[], List.IsChain.nil⟩
  have h := covariance_walk_bound hd (fun v => wordOperator S v x) o rfl hC
    (by simpa only [wordOperator, o, List.map_nil, List.prod_nil,
      one_apply_eq_self] using hcov) n
  rw [iterate_vectorAverage_wordOperator S hS] at h
  simpa only [wordOperator, o, List.map_nil, List.prod_nil,
    one_apply_eq_self] using h

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Koopman
attribute [-instance] _root_.OAI.Problem367.CopyDifference.rangeClosure_completeSpace _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.SpectralClosure.rangeClosure_completeSpace _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.TreeKoopman

theorem average_selfAdjoint (d : ℕ) : IsSelfAdjoint (average d) :=
  koopmanAverage_selfAdjoint _ _ reflection_involutive

theorem centeredAverage_selfAdjoint (d : ℕ) : IsSelfAdjoint (centeredAverage d) :=
  centeredKoopmanAverage_selfAdjoint _ _ _

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WordAction
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanEquiv_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanIsometry_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.koopmanEquiv_apply _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CopyDifference.differenceKoopmanEquiv_apply_coe _root_.OAI.Problem367.CopyDifference.differenceKoopmanIsometry_apply_coe _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

theorem wordAut_root {d : ℕ} (w : List (Fin d))
    (hw : w.IsChain (· ≠ ·)) :
    (wordAut w).toEquiv ⟨[], List.IsChain.nil⟩ = ⟨w, hw⟩ := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change prefixFlip c ((wordAut w).toEquiv ⟨[], List.IsChain.nil⟩) = _
    rw [ih hw.tail]
    apply Subtype.ext
    cases w with
    | nil => rfl
    | cons a w =>
      simp [prefixFlip, prefixFlipWord, (List.isChain_cons_cons.mp hw).1]

theorem list_koopman_eq {d : ℕ} (w : List (Fin d)) :
    (w.map generatorOperator).prod =
      koopmanL2 (wordRelabel w) (wordRelabel_measurePreserving w) := by
  induction w with
  | nil =>
    apply ContinuousLinearMap.ext
    intro f
    change f = Lp.compMeasurePreserving id _ f
    simp
  | cons c w ih =>
    rw [List.map_cons, List.prod_cons, ih]
    apply ContinuousLinearMap.ext
    intro f
    change Lp.compMeasurePreserving (reflection c) _
      (Lp.compMeasurePreserving (wordRelabel w) _ f) =
      Lp.compMeasurePreserving (wordRelabel (c :: w)) _ f
    exact (Lp.compMeasurePreserving_comp_apply f
      (wordRelabel_measurePreserving w) (reflection_measurePreserving c)).symm

theorem wordOperator_eq {d : ℕ} (v : TreeVertex d) :
    RadialWalk.wordOperator generatorOperator v =
      koopmanL2 (wordRelabel v.1) (wordRelabel_measurePreserving v.1) :=
  list_koopman_eq v.1

@[simp] theorem wordOperator_norm {d : ℕ} (v : TreeVertex d)
    (f : Lp ℝ 2 (labelMeasure d)) :
    ‖RadialWalk.wordOperator generatorOperator v f‖ = ‖f‖ := by
  rw [wordOperator_eq, koopmanL2_norm]

theorem operatorAverage_eq {d : ℕ} :
    RadialWalk.operatorAverage (generatorOperator (d := d)) = average d := by
  simp [RadialWalk.operatorAverage, average, koopmanAverage, generatorOperator]

theorem wordOperator_toLp_root {d : ℕ}
    (Z : (TreeVertex d → ℝ) → (TreeVertex d → ℝ))
    (hZ : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Z (relabel g U) = relabel g (Z U))
    (hLp : ∀ v, MemLp (fun U => Z U v) 2 (labelMeasure d))
    (v : TreeVertex d) :
    RadialWalk.wordOperator generatorOperator v
      ((hLp ⟨[], List.IsChain.nil⟩).toLp (fun U => Z U ⟨[], List.IsChain.nil⟩)) =
      (hLp v).toLp (fun U => Z U v) := by
  rw [wordOperator_eq]
  change Lp.compMeasurePreserving (wordRelabel v.1) _
    ((hLp ⟨[], List.IsChain.nil⟩).toLp _) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  filter_upwards [hZ (wordAut v.1).symm] with U hU
  have h := congrFun hU ⟨[], List.IsChain.nil⟩
  change Z (wordRelabel v.1 U) ⟨[], List.IsChain.nil⟩ =
    Z U ((wordAut v.1).toEquiv ⟨[], List.IsChain.nil⟩) at h
  simpa only [Function.comp_apply, wordAut_root v.1 v.2] using h

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CenteredWordAction
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

theorem centered_listProduct_apply_coe {d : ℕ} (w : List (Fin d))
    (f : centeredL2 (labelMeasure d)) :
    ((w.map centeredGenerator).prod f : Lp ℝ 2 (labelMeasure d)) =
      (w.map generatorOperator).prod (f : Lp ℝ 2 (labelMeasure d)) := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    rw [centeredGenerator_apply_coe, ih]

theorem centered_wordOperator_apply_coe {d : ℕ} (v : TreeVertex d)
    (f : centeredL2 (labelMeasure d)) :
    (RadialWalk.wordOperator centeredGenerator v f : Lp ℝ 2 (labelMeasure d)) =
      RadialWalk.wordOperator generatorOperator v (f : Lp ℝ 2 (labelMeasure d)) :=
  centered_listProduct_apply_coe v.1 f

theorem centered_operatorAverage_eq {d : ℕ} :
    RadialWalk.operatorAverage (centeredGenerator (d := d)) = centeredAverage d := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  rw [centeredAverage_apply_coe]
  simp only [RadialWalk.operatorAverage, smul_apply, sum_apply,
    Submodule.coe_smul, Submodule.coe_sum, centeredGenerator_apply_coe]
  rw [← operatorAverage_eq, RadialWalk.operatorAverage_apply]

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FairSpin
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma fairSpin_neg_preimage : fairSpin ⁻¹' {IsingSpin.neg} = Set.Iic (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin]

lemma fairSpin_pos_preimage : fairSpin ⁻¹' {IsingSpin.pos} = Set.Ioi (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin, not_le]

lemma fairSpin_neg_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.neg}) = 1 / 2 := by
  rw [fairSpin_neg_preimage, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨h0, hu⟩
    · rintro ⟨h0, hu⟩
      exact ⟨hu, h0, by linarith⟩
  rw [h, Real.volume_Icc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_pos_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.pos}) = 1 / 2 := by
  rw [fairSpin_pos_preimage, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨hu, h1⟩
    · rintro ⟨hu, h1⟩
      exact ⟨hu, by linarith, h1⟩
  rw [h, Real.volume_Ioc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_mass (a : IsingSpin) : uniform01 (fairSpin ⁻¹' {a}) = 1 / 2 := by
  cases a
  · exact fairSpin_neg_mass
  · exact fairSpin_pos_mass

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteChain
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367.FiniteChain

variable {A : Type*}

theorem weight_eq_prod (K : A → A → ℝ) (n : ℕ) (a : A) (x : Fin n → A) :
    weight K n a x = ∏ i : Fin n, K ((Fin.cons a x : Fin (n+1) → A) i.castSucc) (x i) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [weight, Fin.prod_univ_succ, ih]
    simp [Fin.tail]

theorem endpoint_eq_last (n : ℕ) (a : A) (x : Fin n → A) :
    endpoint n a x = (Fin.cons a x : Fin (n+1) → A) (Fin.last n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [endpoint, ih]
    simp

variable [Fintype A]

theorem sum_cons (n : ℕ) (f : (Fin (n+1) → A) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → A, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

theorem expectation_succ (K : A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) :
    expectation K (n+1) f a = ∑ b, K a b * expectation K n f b := by
  unfold expectation
  rw [sum_cons]
  simp only [weight_cons, endpoint_cons, mul_assoc, Finset.mul_sum]

theorem expectation_eigenfunction (K : A → A → ℝ) (f : A → ℝ) (r : ℝ)
    (hf : ∀ a, ∑ b, K a b * f b = r * f a) (n : ℕ) (a : A) :
    expectation K n f a = r^n * f a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [expectation_succ]
    simp_rw [ih]
    calc
      ∑ b, K a b * (r ^ n * f b) = r ^ n * ∑ b, K a b * f b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = r ^ (n+1) * f a := by rw [hf, pow_succ]; ring

end Problem367.FiniteChain

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LabelDecomposition
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.LabelDecomposition

theorem indepFun_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    IndepFun (fun U : ι → A => U r)
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i)
      (Measure.infinitePi μ) := by
  have hi : iIndepFun (fun i (U : ι → A) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → A => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → A)) :=
    fun i => measurable_iff_comap_le.mp (measurable_pi_apply i)
  have hd : Disjoint ({r} : Set ι) {i | i ≠ r} := by simp
  have h := indep_iSup_of_disjoint hle hi hd
  change Indep (MeasurableSpace.comap (fun U : ι → A => U r) inferInstance)
    (MeasurableSpace.comap
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i) inferInstance)
    (Measure.infinitePi μ)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

theorem map_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    (Measure.infinitePi μ).map
      (fun U : ι → A => (U r, fun i : {i : ι // i ≠ r} => U i)) =
      (μ r).prod (Measure.infinitePi (fun i : {i : ι // i ≠ r} => μ i)) := by
  rw [(indepFun_coordinate_rest μ r).map_prod_eq_prod_map_map
    (measurable_pi_apply r).aemeasurable
      ((measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1)).aemeasurable)]
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

theorem map_fairSpin_rest (d : ℕ) (r : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (fairSpin (U r), fun v : {v : TreeVertex d // v ≠ r} => U v)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : {v : TreeVertex d // v ≠ r} => uniform01)) := by
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map _ = _
  have hrest : Measurable
      (fun U : TreeVertex d → ℝ => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v)) :=
    (measurable_pi_apply r).prodMk
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1))
  calc
    _ = ((Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map
        (fun U => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v))).map
          (Prod.map fairSpin id) := by
      rw [Measure.map_map (measurable_fairSpin.prodMap measurable_id) hrest]
      rfl
    _ = _ := by
      rw [map_coordinate_rest,
        ← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]

end Problem367.LabelDecomposition

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_UniformTwist
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurePreserving_fiberTwist
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (twist : B → A → A)
    (hmeas : Measurable (fun p : A × B => twist p.2 p.1))
    (hpres : ∀ b, MeasurePreserving (twist b) μ μ) :
    MeasurePreserving (fun p : A × B => (twist p.2 p.1, p.2))
      (μ.prod ν) (μ.prod ν) := by
  have hm : Measurable (fun p : A × B => (twist p.2 p.1, p.2)) :=
    hmeas.prodMk measurable_snd
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hs.preimage hm),
    Measure.prod_apply_symm hs]
  apply lintegral_congr
  intro b
  change μ ((twist b) ⁻¹' ((fun a => (a, b)) ⁻¹' s)) =
    μ ((fun a => (a, b)) ⁻¹' s)
  exact (hpres b).measure_preimage ((hs.preimage measurable_prodMk_right).nullMeasurableSet)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordOperator_norm _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_lower_unique {d : ℕ} {u v w : TreeVertex d}
    (hu : treeAdj u w) (hv : treeAdj v w)
    (huw : u.1.length < w.1.length) (hvw : v.1.length < w.1.length) : u = v := by
  exact (treeAdj_parent_of_length_lt hu huw).symm.trans
    (treeAdj_parent_of_length_lt hv hvw)

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcast
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordOperator_norm _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

attribute [local instance] OAI.Problem367.RootedBroadcast.rootedBroadcastMeasurableSingletonSpin
lemma spinMul_comm (a b : IsingSpin) : spinMul a b = spinMul b a := by
  cases a <;> cases b <;> rfl
lemma spinMul_assoc (a b c : IsingSpin) : spinMul (spinMul a b) c = spinMul a (spinMul b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] lemma spinMul_cancel (a b : IsingSpin) : spinMul a (spinMul a b) = b := by
  rw [← spinMul_assoc, spinMul_self, pos_spinMul]

lemma biasedSpin_pos_mass {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.pos}) = ENNReal.ofReal p := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.pos} = Set.Iic p := by
    ext u
    simp [biasedSpin]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic p ∩ Set.Icc 0 1 = Set.Icc 0 p := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨hu,h0,_⟩ => ⟨h0,hu⟩, fun ⟨h0,hu⟩ => ⟨hu,h0,hu.trans hp1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

lemma biasedSpin_neg_mass {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.neg}) = ENNReal.ofReal (1-p) := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.neg} = Set.Ioi p := by
    ext u
    simp [biasedSpin, not_le]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi p ∩ Set.Icc 0 1 = Set.Ioc p 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨hu,_,h1⟩ => ⟨hu,h1⟩, fun ⟨hu,h1⟩ => ⟨hu,hp0.trans hu.le,h1⟩⟩
  rw [h, Real.volume_Ioc]

lemma ofNoise_root {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    ofNoise noise ⟨[], List.isChain_nil⟩ = noise ⟨[], List.isChain_nil⟩ := by
  rw [ofNoise]
  simp

@[simp] lemma noiseFromSpins_ofNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    noiseFromSpins (ofNoise noise) = noise := by
  funext v
  by_cases hv : v.val = []
  · rw [noiseFromSpins, ite_eq_left hv, ofNoise]
    simp [hv]
  · rw [noiseFromSpins, ite_eq_right hv, ofNoise_nonroot noise v hv]
    rw [spinMul_assoc, spinMul_self, spinMul_pos]

@[simp] lemma ofNoise_noiseFromSpins {d : ℕ} (x : TreeVertex d → IsingSpin) :
    ofNoise (noiseFromSpins x) = x := by
  funext v
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise (noiseFromSpins x) v = x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · rw [ofNoise]
        simp [hnil, noiseFromSpins]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot _ v hnil, ih _ hlt (parent v) rfl,
          noiseFromSpins, ite_eq_right hnil, spinMul_assoc, spinMul_self, spinMul_pos]
  exact h _ v rfl

lemma edgeNoise_mass {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (a : IsingSpin) :
    uniform01 ((edgeNoise theta) ⁻¹' {a}) =
      ENNReal.ofReal ((1 + (if a = IsingSpin.pos then theta else -theta)) / 2) := by
  have hp0 : 0 ≤ (1 + theta) / 2 := by linarith
  have hp1 : (1 + theta) / 2 ≤ 1 := by linarith
  cases a
  · rw [edgeNoise, biasedSpin_neg_mass hp0 hp1, ite_eq_right (by decide : IsingSpin.neg ≠ IsingSpin.pos)]
    congr 1
    ring
  · rw [edgeNoise, biasedSpin_pos_mass hp0 hp1]
    rfl

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Twist
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance localInst_r024166_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem measurePreserving_fairSpin_mul (b : IsingSpin) :
    MeasurePreserving (fun a => spinMul a b)
      (uniform01.map fairSpin) (uniform01.map fairSpin) := by
  have hm : Measurable (fun a => spinMul a b) := measurable_of_finite _
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_singleton
  intro a
  have hpre : (fun x => spinMul x b) ⁻¹' {a} = {spinMul a b} := by
    ext x
    cases x <;> cases a <;> cases b <;> simp [spinMul]
  rw [Measure.map_apply hm (measurableSet_singleton a), hpre,
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _),
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass,
    fairSpin_mass]

theorem measurePreserving_fairSpin_twist
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {f : Y → IsingSpin} (hf : Measurable f) :
    MeasurePreserving (fun p : IsingSpin × Y => (spinMul p.1 (f p.2), p.2))
      ((uniform01.map fairSpin).prod ν) ((uniform01.map fairSpin).prod ν) := by
  apply measurePreserving_fiberTwist (uniform01.map fairSpin) ν
    (fun y a => spinMul a (f y))
  · exact measurable_spinMul.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  · intro y
    exact measurePreserving_fairSpin_mul (f y)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Cardinality
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

private lemma mem_inducedEdges_8911 {d : ℕ} (D : Finset (TreeVertex d))
    (u v : TreeVertex d) :
    (u, v) ∈ inducedEdges D ↔
      (u ∈ D ∧ v ∈ D) ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  rw [inducedEdges, Finset.mem_filter]
  exact and_congr Finset.mem_product Iff.rfl

lemma inducedEdges_snd_injOn {d : ℕ} (D : Finset (TreeVertex d)) :
    Set.InjOn Prod.snd (↑(inducedEdges D) : Set (TreeVertex d × TreeVertex d)) := by
  rintro ⟨a, b⟩ hab ⟨c, e⟩ hce heq
  have hab' : (a ∈ D ∧ b ∈ D) ∧ treeAdj a b ∧ a.1.length < b.1.length := by
    exact (mem_inducedEdges_8911 D a b).mp hab
  have hce' : (c ∈ D ∧ e ∈ D) ∧ treeAdj c e ∧ c.1.length < e.1.length := by
    exact (mem_inducedEdges_8911 D c e).mp hce
  change b = e at heq
  subst e
  exact Prod.ext (treeAdj_lower_unique hab'.2.1 hce'.2.1 hab'.2.2 hce'.2.2) rfl

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SpinEncoding
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma spinAgreementCode_comm (a b : IsingSpin) :
    spinAgreementCode a b = spinAgreementCode b a := by
  cases a <;> cases b <;> rfl

lemma ConnectedFinset.spin_eq_on_iff_root_agreements {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (σ τ : TreeVertex d → IsingSpin) :
    (∀ v ∈ D, σ v = τ v) ↔
      σ r = τ r ∧ ∀ e ∈ inducedEdges D,
        spinAgreementCode (σ e.1) (σ e.2) =
          spinAgreementCode (τ e.1) (τ e.2) := by
  classical
  constructor
  · intro h
    refine ⟨h r hr, ?_⟩
    intro e he
    have heD := Finset.mem_product.mp (Finset.mem_filter.mp he).1
    rw [h e.1 heD.1, h e.2 heD.2]
  · rintro ⟨hroot, hedges⟩
    have step {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D)
        (hadj : treeAdj u v) (heq : σ u = τ u) : σ v = τ v := by
      have hcode : spinAgreementCode (σ u) (σ v) =
          spinAgreementCode (τ u) (τ v) := by
        rcases treeAdj_length hadj with hlen | hlen
        · apply hedges (u, v)
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj, by change u.1.length < v.1.length; omega⟩
        · have his : (v, u) ∈ inducedEdges D := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨hv, hu⟩, Or.symm hadj, by change v.1.length < u.1.length; omega⟩
          simpa only [spinAgreementCode_comm (σ v) (σ u),
            spinAgreementCode_comm (τ v) (τ u)] using hedges (v, u) his
      rw [heq] at hcode
      exact spinAgreementCode_injective_right (τ u) hcode
    intro v hv
    have hpath := hD.2 r hr v hv
    induction hpath with
    | refl => exact hroot
    | tail hpath hadj ih => exact step hadj.1 hadj.2.1 hadj.2.2 (ih hadj.1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcastLaw
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordOperator_norm _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastLawMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩

lemma eq_root_iff {d : ℕ} (v : TreeVertex d) : v = root d ↔ v.val = [] := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact h

lemma ofNoise_root_decomposition {d : ℕ} (noise : TreeVertex d → IsingSpin)
    (v : TreeVertex d) :
    ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · have hvroot : v = root d := (eq_root_iff v).mpr hnil
        subst v
        simp [root, ofNoise_root, eraseRootNoise]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise v hnil, ofNoise_nonroot (eraseRootNoise noise) v hnil,
          eraseRootNoise, ite_eq_right hnil, ih _ hlt (parent v) rfl]
        rw [← spinMul_assoc, spinMul_comm (noise v) (noise (root d)), spinMul_assoc]
  exact h _ v rfl

lemma measurable_nonrootNoise (d : ℕ) (theta : ℝ) : Measurable (@nonrootNoise d theta) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v = root d
  · simpa only [nonrootNoise, dite_eq_left hv] using
      (measurable_const : Measurable (fun _ : NonrootVertex d → ℝ => IsingSpin.pos))
  · simpa only [nonrootNoise, dite_eq_right hv, Function.comp_def] using
      (measurable_edgeNoise theta).comp (measurable_pi_apply (X := fun _ : NonrootVertex d => ℝ) ⟨v, hv⟩)

lemma measurable_rootlessFactor (d : ℕ) (theta : ℝ) : Measurable (@rootlessFactor d theta) :=
  (measurable_ofNoise d).comp (measurable_nonrootNoise d theta)

lemma factor_root_decomposition {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    (v : TreeVertex d) :
    factor theta U v = spinMul (fairSpin (U (root d)))
      (rootlessFactor theta (fun w : NonrootVertex d => U w.val) v) := by
  rw [factor, ofNoise_root_decomposition]
  have heq : eraseRootNoise (inputNoise theta U) =
      nonrootNoise theta (fun w : NonrootVertex d => U w.val) := by
    funext w
    by_cases hw : w = root d
    · subst w
      simp [eraseRootNoise, nonrootNoise]
    · have hnil : w.val ≠ [] := fun h => hw ((eq_root_iff w).mpr h)
      simp [eraseRootNoise, inputNoise, nonrootNoise, hw, hnil]
  rw [heq]
  rfl

lemma factor_edge_agreement {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    {u v : TreeVertex d} (huv : treeAdj u v) (hlt : u.val.length < v.val.length) :
    spinAgreementCode (factor theta U u) (factor theta U v) = edgeNoise theta (U v) := by
  have hp : parent v = u := treeAdj_parent_of_length_lt huv hlt
  have hnil : v.val ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlt
    omega
  change spinMul (factor theta U u) (factor theta U v) = _
  change spinMul (ofNoise (inputNoise theta U) u) (ofNoise (inputNoise theta U) v) = _
  rw [ofNoise_nonroot _ v hnil, hp]
  simp only [inputNoise, ite_eq_right hnil]
  rw [spinMul_comm (edgeNoise theta (U v)), spinMul_cancel]

lemma factor_cylinder_event {d : ℕ} (theta : ℝ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (eta : TreeVertex d → IsingSpin) :
    {U : TreeVertex d → ℝ | ∀ v ∈ D, factor theta U v = eta v} =
      {U | factor theta U r = eta r ∧ ∀ e ∈ inducedEdges D,
        edgeNoise theta (U e.2) = spinAgreementCode (eta e.1) (eta e.2)} := by
  classical
  ext U
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hD.spin_eq_on_iff_root_agreements hr]
  apply and_congr_right
  intro hroot
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  have he' := (Finset.mem_filter.mp he).2
  rw [factor_edge_agreement theta U he'.1 he'.2]

lemma edgeVertex_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (edgeVertex D) := by
  intro a b hab
  apply Subtype.ext
  apply inducedEdges_snd_injOn D a.property b.property
  exact congrArg Subtype.val hab

lemma nonroot_edge_event_mass {d : ℕ} {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))
      {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
        spinAgreementCode (eta e.val.1) (eta e.val.2)} =
      ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  classical
  let A : Set ((e : inducedEdges D) → ℝ) := Set.pi Set.univ
    (fun e => edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)})
  have hA : MeasurableSet A := MeasurableSet.univ_pi
    (fun e => (measurable_edgeNoise theta) (measurableSet_singleton _))
  have hm : Measurable (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e)) := by
    fun_prop
  calc
    _ = (Measure.map (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e))
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) A := by
      rw [Measure.map_apply hm hA]
      congr 1
      ext Y
      simp [A, Set.mem_pi]
    _ = (Measure.infinitePi (fun _ : inducedEdges D => uniform01)) A := by
      rw [Measure.map_infinitePi_infinitePi_of_inj (edgeVertex_injective D)]
    _ = ∏ e : inducedEdges D, uniform01
        (edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)}) := by
      simpa only [A, Finset.coe_univ] using
        (Measure.infinitePi_pi (fun _ : inducedEdges D => uniform01)
          (s := Finset.univ) (fun e _ => (measurable_edgeNoise theta)
            (measurableSet_singleton (spinAgreementCode (eta e.val.1) (eta e.val.2)))))
    _ = _ := by
      simp only [edgeNoise_mass h0 h1, spinAgreementCode_eq_pos_iff]
      exact Finset.prod_coe_sort (inducedEdges D) (fun e : TreeVertex d × TreeVertex d =>
        ENNReal.ofReal ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

lemma freeCylinderWeight_eq_edge_product {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  unfold freeCylinderWeight
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · norm_num [ENNReal.ofReal_div_of_pos]
  · intro e he
    split_ifs <;> linarith

lemma hasFreeIsingLaw_of_root_nonroot_joint {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (hjoint : ∀ r : TreeVertex d,
      (labelMeasure d).map (fun U => (factor theta U r, fun w : NonrootVertex d => U w.val)) =
        (uniform01.map fairSpin).prod (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) :
    HasFreeIsingLaw theta ((labelMeasure d).map (factor theta)) := by
  classical
  intro D hD eta
  obtain ⟨r, hr⟩ := hD.1
  let A : Set (NonrootVertex d → ℝ) :=
    {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
      spinAgreementCode (eta e.val.1) (eta e.val.2)}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro e
    exact ((measurable_edgeNoise theta).comp (measurable_pi_apply (edgeVertex D e)))
      (measurableSet_singleton _)
  have hS : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet (fun v _ => measurableSet_singleton (eta v))
  have hm : Measurable (fun U : TreeVertex d → ℝ =>
      (factor theta U r, fun w : NonrootVertex d => U w.val)) := by
    exact ((measurable_pi_apply r).comp (measurable_factor d theta)).prodMk
      (Measurable.of_eval (fun w => measurable_pi_apply w.val))
  rw [Measure.map_apply (measurable_factor d theta) hS]
  change (labelMeasure d) {U | ∀ v ∈ D, factor theta U v = eta v} = _
  rw [factor_cylinder_event theta D hD r hr eta]
  calc
    _ = ((labelMeasure d).map (fun U =>
        (factor theta U r, fun w : NonrootVertex d => U w.val))) ({eta r} ×ˢ A) := by
      rw [Measure.map_apply hm ((measurableSet_singleton _).prod hA)]
      congr 1
      ext U
      simp [A, Set.mem_prod, edgeVertex]
    _ = ((uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) ({eta r} ×ˢ A) := by
      rw [hjoint r]
    _ = (uniform01.map fairSpin) {eta r} *
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A :=
      Measure.prod_prod _ _
    _ = (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
      rw [Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass]
      rw [show (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A = _ from
        nonroot_edge_event_mass h0 h1 D eta]
    _ = freeCylinderWeight theta D eta := (freeCylinderWeight_eq_edge_product h0 h1 D eta).symm

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastJointLaw
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem map_factor_rest (d : ℕ) (theta : ℝ) (v : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (factor theta U v, fun w : NonrootVertex d => U w.val)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) := by
  have hf : Measurable (fun Y : NonrootVertex d → ℝ => rootlessFactor theta Y v) :=
    (measurable_pi_apply v).comp (measurable_rootlessFactor d theta)
  have ht := measurePreserving_fairSpin_twist
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) hf
  have hj : Measurable (fun U : TreeVertex d → ℝ =>
      (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val)) :=
    (measurable_fairSpin.comp (measurable_pi_apply (root d))).prodMk
      (measurable_pi_iff.mpr (fun w => measurable_pi_apply w.val))
  calc
    _ = ((labelMeasure d).map
        (fun U => (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val))).map
          (fun p : IsingSpin × (NonrootVertex d → ℝ) =>
            (spinMul p.1 (rootlessFactor theta p.2 v), p.2)) := by
      rw [Measure.map_map ht.measurable hj]
      congr 1
      funext U
      exact Prod.ext (factor_root_decomposition theta U v) rfl
    _ = _ := by
      rw [LabelDecomposition.map_fairSpin_rest]
      exact ht.map_eq

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeIsingMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem freeIsingMeasure_hasFreeIsingLaw (d : ℕ) {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) :
    HasFreeIsingLaw theta (freeIsingMeasure d theta) :=
  RootedBroadcast.hasFreeIsingLaw_of_root_nonroot_joint h0 h1
    (RootedBroadcast.map_factor_rest d theta)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_LocalOrthogonality
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem indepFun_of_disjoint_finite_blocks (s t : Finset ι) (hst : Disjoint s t)
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : (∀ i : s, X i) → α) (g : (∀ i : t, X i) → β)
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun U : ∀ i, X i => f (fun i => U i))
      (fun U : ∀ i, X i => g (fun i => U i)) (Measure.infinitePi μ) := by
  have hind : iIndepFun (fun i (U : ∀ i, X i) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  exact (hind.indepFun_finset s t hst (fun i => measurable_pi_apply i)).comp hf hg

section Reindex

variable {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]

theorem indepFun_finite_blocks_reindex (s t : Finset ι) (e : ι ≃ ι)
    (hst : Disjoint s (t.map e.toEmbedding))
    (f : (s → A) → ℝ) (g : (t → A) → ℝ) (hf : Measurable f) (hg : Measurable g) :
    IndepFun (fun U : ι → A => f (fun i => U i))
      (fun U : ι → A => g (fun i => U (e i))) (Measure.infinitePi fun _ : ι => ν) := by
  let G : (t.map e.toEmbedding → A) → ℝ := fun U =>
    g (fun i => U ⟨e i, Finset.mem_map.2 ⟨i, i.property, rfl⟩⟩)
  have hG : Measurable G := by
    apply hg.comp
    fun_prop
  simpa [G] using indepFun_of_disjoint_finite_blocks (fun _ : ι => ν)
    s (t.map e.toEmbedding) hst f G hf hG

theorem integral_mul_reindex_eq_zero_of_disjoint (s t : Finset ι) (e : ι ≃ ι)
    (hst : Disjoint s (t.map e.toEmbedding))
    (f : (s → A) → ℝ) (g : (t → A) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hzero : (∫ U, f (fun i => U i) ∂Measure.infinitePi (fun _ : ι => ν)) = 0) :
    (∫ U, f (fun i => U i) * g (fun i => U (e i))
      ∂Measure.infinitePi (fun _ : ι => ν)) = 0 := by
  have hind := indepFun_finite_blocks_reindex ν s t e hst f g hf hg
  rw [hind.integral_fun_mul_eq_mul_integral
    (Measurable.aestronglyMeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop)), hzero, zero_mul]

end Reindex

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Escape
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordOperator_norm _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace TreeEscape

private theorem adj_depth_le {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    u.1.length ≤ v.1.length + 1 := by
  rcases h with ⟨c, h⟩ | ⟨c, h⟩
  · have hlen := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  · have hlen := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hlen
    omega

theorem root_depth_le {d : ℕ} (g : TreeAut d) (v : TreeVertex d) :
    (g.toEquiv root).1.length ≤ (g.toEquiv v).1.length + v.1.length := by
  rcases v with ⟨w, hw⟩
  induction w using List.reverseRecOn with
  | nil => simp [root]
  | append_singleton w a ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.left_of_append
    have ih' := ih hw'
    change (g.toEquiv root).1.length ≤
      (g.toEquiv ⟨w, hw'⟩).1.length + w.length at ih'
    have hadj : treeAdj (⟨w, hw'⟩ : TreeVertex d) ⟨w ++ [a], hw⟩ :=
      Or.inl ⟨a, rfl⟩
    have hlen := adj_depth_le ((g.map_adj _ _).2 hadj)
    simp only [List.length_append, List.length_singleton]
    omega

theorem symm_root_depth {d : ℕ} (g : TreeAut d) :
    (g.toEquiv.symm root).1.length = (g.toEquiv root).1.length := by
  have h₁ := root_depth_le g (g.toEquiv.symm root)
  have h₂ := root_depth_le g.symm (g.toEquiv root)
  change (g.toEquiv.symm root).1.length ≤
    (g.toEquiv.symm (g.toEquiv root)).1.length + (g.toEquiv root).1.length at h₂
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    show (root : TreeVertex d).1.length = 0 from rfl, zero_add] at h₁ h₂
  exact Nat.le_antisymm h₂ h₁

theorem disjoint_image_of_root_depth {d : ℕ} (g : TreeAut d)
    (S T : Finset (TreeVertex d))
    (h : S.sup (fun v => v.1.length) + T.sup (fun v => v.1.length) <
      (g.toEquiv root).1.length) :
    Disjoint (S.image g.toEquiv) T := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hvt
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  have hlen := root_depth_le g u
  have hu' : u.1.length ≤ S.sup (fun v => v.1.length) :=
    Finset.le_sup (f := fun v : TreeVertex d => v.1.length) hu
  have hv' : (g.toEquiv u).1.length ≤ T.sup (fun v => v.1.length) :=
    Finset.le_sup (f := fun v : TreeVertex d => v.1.length) hvt
  omega

theorem disjoint_inverse_image_of_root_depth {d : ℕ} (g : TreeAut d)
    (S T : Finset (TreeVertex d))
    (h : S.sup (fun v => v.1.length) + T.sup (fun v => v.1.length) <
      (g.toEquiv root).1.length) :
    Disjoint (S.image g.toEquiv.symm) T := by
  apply disjoint_image_of_root_depth g.symm S T
  change _ < (g.toEquiv.symm root).1.length
  rwa [symm_root_depth]

end TreeEscape

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LocalCorrelation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanEquiv_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanIsometry_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.koopmanEquiv_apply _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CopyDifference.differenceKoopmanEquiv_apply_coe _root_.OAI.Problem367.CopyDifference.differenceKoopmanIsometry_apply_coe _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordOperator_norm _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem local_koopman_inner_eq_zero_of_depth {d : ℕ}
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (labelMeasure d))
    (F : (s → ℝ) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[labelMeasure d] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂labelMeasure d) = 0)
    (g : TreeAut d)
    (hdepth : s.sup (fun v => v.1.length) + s.sup (fun v => v.1.length) <
      (g.toEquiv TreeEscape.root).1.length) :
    inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f) = 0 := by
  classical
  have hdisj : Disjoint s (s.map g.toEquiv.symm.toEmbedding) := by
    rw [Finset.map_eq_image]
    exact (TreeEscape.disjoint_inverse_image_of_root_depth g s s hdepth).symm
  have hFzero : (∫ U, F (fun i => U i) ∂labelMeasure d) = 0 :=
    (integral_congr_ae hf).symm.trans hzero
  have hright := (measurePreserving_relabel g).quasiMeasurePreserving.ae hf
  have hkoop := Lp.coeFn_compMeasurePreserving f (measurePreserving_relabel g)
  calc
    inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f) =
        ∫ U, F (fun i => U i) * F (fun i => U (g.toEquiv.symm i))
          ∂labelMeasure d := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf, hright, hkoop] with U hU hUg hK
      change koopmanL2 (relabel g) (measurePreserving_relabel g) f U = f (relabel g U) at hK
      simp [hK, hU, hUg, relabel, mul_comm]
    _ = 0 := integral_mul_reindex_eq_zero_of_disjoint uniform01 s s g.toEquiv.symm
      hdisj F F hF hF hFzero

theorem exists_local_koopman_radial_bound {d : ℕ}
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (labelMeasure d))
    (F : (s → ℝ) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[labelMeasure d] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂labelMeasure d) = 0)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : TreeAut d,
      |inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f)| ≤
        C * q ^ (g.toEquiv TreeEscape.root).1.length := by
  let N := s.sup (fun v => v.1.length) + s.sup (fun v => v.1.length)
  let C := ‖f‖ ^ 2 / q ^ N
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) (pow_nonneg hq.le _)
  refine ⟨C, hC, ?_⟩
  intro g
  by_cases hn : N < (g.toEquiv TreeEscape.root).1.length
  · rw [local_koopman_inner_eq_zero_of_depth s f F hF hf hzero g hn, abs_zero]
    exact mul_nonneg hC (pow_nonneg hq.le _)
  · have hpow : q ^ N ≤ q ^ (g.toEquiv TreeEscape.root).1.length :=
      pow_le_pow_of_le_one hq.le hq1 (Nat.le_of_not_gt hn)
    calc
      |inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f)| ≤
          ‖f‖ * ‖koopmanL2 (relabel g) (measurePreserving_relabel g) f‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖f‖ ^ 2 := by rw [koopmanL2_norm, pow_two]
      _ = C * q ^ N := by
        dsimp [C]
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hq.ne')]
      _ ≤ C * q ^ (g.toEquiv TreeEscape.root).1.length :=
        mul_le_mul_of_nonneg_left hpow hC

theorem exists_local_koopman_critical_bound {d : ℕ} (hd : 3 ≤ d)
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (labelMeasure d))
    (F : (s → ℝ) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[labelMeasure d] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂labelMeasure d) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : TreeAut d,
      |inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f)| ≤
        C * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ (g.toEquiv TreeEscape.root).1.length := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  apply exists_local_koopman_radial_bound s f F hF hf hzero (inv_pos.mpr hs)
  apply inv_le_one_of_one_le₀
  apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ (d : ℝ) - 1)).2
  norm_num
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Moments
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

attribute [local instance] OAI.Problem367.spinMomentsMeasurableSingleton
theorem IsingSpin.toReal_eq_spinSign (s : IsingSpin) : s.toReal = spinSign s := by
  cases s <;> rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Chain
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem spinPathWeight_cons (theta : ℝ) (n : ℕ) (a : IsingSpin)
    (x : Fin n → IsingSpin) :
    spinPathWeight theta n (Fin.cons a x) =
      FiniteChain.weight (transitionKernel theta) n a x := by
  rw [FiniteChain.weight_eq_prod]
  simp [spinPathWeight]

theorem spinChain_expectation (theta : ℝ) (n : ℕ) (a : IsingSpin) :
    ∑ x : Fin n → IsingSpin,
      FiniteChain.weight (transitionKernel theta) n a x *
        spinSign (FiniteChain.endpoint n a x) = theta^n * spinSign a :=
  FiniteChain.expectation_eigenfunction (transitionKernel theta) spinSign theta
    (transitionKernel_spinSum theta) n a

theorem spinPathWeight_correlation (theta : ℝ) (n : ℕ) :
    ∑ x : Fin (n+1) → IsingSpin,
      (1/2 : ℝ) * spinPathWeight theta n x * spinSign (x 0) *
        spinSign (x (Fin.last n)) = theta^n := by
  rw [FiniteChain.sum_cons]
  simp only [spinPathWeight_cons, Fin.cons_zero,
    ← FiniteChain.endpoint_eq_last]
  have hinner (a : IsingSpin) :
      (∑ x : Fin n → IsingSpin,
        (1/2 : ℝ) * FiniteChain.weight (transitionKernel theta) n a x * spinSign a *
          spinSign (FiniteChain.endpoint n a x)) = (1/2 : ℝ) * theta^n := by
    calc
      _ = (1/2 : ℝ) * spinSign a *
          ∑ x : Fin n → IsingSpin,
            FiniteChain.weight (transitionKernel theta) n a x *
              spinSign (FiniteChain.endpoint n a x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (1/2 : ℝ) * theta^n := by
        rw [spinChain_expectation]
        calc
          _ = (1/2 : ℝ) * theta^n * (spinSign a * spinSign a) := by ring
          _ = _ := by rw [spinSign_mul_self, mul_one]
  simp_rw [hinner]
  rw [sum_isingSpin]
  ring

theorem spinPathWeight_nonneg {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (n : ℕ) (x : Fin (n+1) → IsingSpin) : 0 ≤ spinPathWeight theta n x := by
  exact Finset.prod_nonneg fun _ _ => transitionKernel_nonneg hlo hhi _ _

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteLawIntegral
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordOperator_norm _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem integral_finiteLaw {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Fintype E] [MeasurableSingletonClass E]
    {mu : Measure Ω} [IsFiniteMeasure mu] {X : Ω → E} (hX : Measurable X)
    (weight : E → ℝ) (hweight : ∀ e, 0 ≤ weight e)
    (hlaw : ∀ e, mu {ω | X ω = e} = ENNReal.ofReal (weight e)) (f : E → ℝ) :
    ∫ ω, f (X ω) ∂mu = ∑ e : E, weight e * f e := by
  rw [← integral_map hX.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
  rw [integral_fintype (Integrable.of_finite : Integrable f (Measure.map X mu))]
  apply Finset.sum_congr rfl
  intro e he
  rw [Measure.real, Measure.map_apply hX (measurableSet_singleton e)]
  change (mu {ω | X ω = e}).toReal * f e = weight e * f e
  rw [hlaw e, ENNReal.toReal_ofReal (hweight e)]

local instance localInst_r024166_2 : MeasurableSingletonClass IsingSpin where
  measurableSet_singleton _ := by trivial
theorem integral_finiteSpinCoordinates {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (p : I → TreeVertex d) (weight : (I → IsingSpin) → ℝ)
    (hweight : ∀ eta, 0 ≤ weight eta)
    (hlaw : ∀ eta, mu {x | ∀ i, x (p i) = eta i} = ENNReal.ofReal (weight eta))
    (f : (I → IsingSpin) → ℝ) :
    ∫ x, f (fun i => x (p i)) ∂mu = ∑ eta : I → IsingSpin, weight eta * f eta := by
  refine integral_finiteLaw (X := fun x : TreeVertex d → IsingSpin => fun i => x (p i))
    (Measurable.of_eval (fun index => measurable_pi_apply (p index))) weight hweight ?_ f
  intro eta
  convert hlaw eta using 2
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_ofPred_eq, funext_iff]

theorem integral_spinPath_of_cylinderLaw {d n : ℕ} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (p : Fin (n+1) → TreeVertex d)
    (hlaw : ∀ eta : Fin (n+1) → IsingSpin,
      mu {x | ∀ i, x (p i) = eta i} =
        ENNReal.ofReal ((1/2 : ℝ) * spinPathWeight theta n eta)) :
    ∫ x, spinSign (x (p 0)) * spinSign (x (p (Fin.last n))) ∂mu = theta ^ n := by
  calc
    _ = ∑ eta : Fin (n+1) → IsingSpin,
        ((1/2 : ℝ) * spinPathWeight theta n eta) *
          (spinSign (eta 0) * spinSign (eta (Fin.last n))) :=
      integral_finiteSpinCoordinates p _
        (fun eta => mul_nonneg (by norm_num) (spinPathWeight_nonneg hlo hhi n eta))
        hlaw _
    _ = theta ^ n := by
      simpa only [mul_assoc] using spinPathWeight_correlation theta n

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCylinders
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordOperator_norm _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
namespace Problem367
namespace ConnectedHull

theorem connected_vertices {d : ℕ} (v : TreeVertex d) :
    ConnectedFinset (vertices v) := by
  have hmem : ∀ n ≤ v.1.length, takeVertex v n ∈ vertices v :=
    fun _ hn => prefix_mem_vertices v hn
  refine ⟨⟨root d, by simpa using hmem 0 (Nat.zero_le _)⟩, ?_⟩
  intro u hu w hw
  obtain ⟨i, hi, rfl⟩ := mem_vertices.mp hu
  obtain ⟨j, hj, rfl⟩ := mem_vertices.mp hw
  exact (prefix_paths (vertices v) v hmem hi).2.trans
    (prefix_paths (vertices v) v hmem hj).1

theorem pathEdge_injective {d : ℕ} (v : TreeVertex d) :
    Function.Injective (pathEdge v) := by
  intro i j h
  have hi := path_injective v (congrArg Prod.fst h)
  exact Fin.ext (congrArg (fun x : Fin (v.1.length+1) => x.val) hi)

theorem vertices_eq_image_path {d : ℕ} (v : TreeVertex d) :
    vertices v = Finset.univ.image (path v) := by
  classical
  ext u
  simp only [mem_vertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, heq⟩
    exact ⟨⟨n, by omega⟩, heq⟩
  · rintro ⟨i, heq⟩
    exact ⟨i, by omega, heq⟩

theorem inducedEdges_vertices {d : ℕ} (v : TreeVertex d) :
    inducedEdges (vertices v) = Finset.univ.image (pathEdge v) := by
  classical
  ext e
  rcases e with ⟨u,w⟩
  constructor
  · intro he
    obtain ⟨hmem, hadj, hlt⟩ := Finset.mem_filter.mp he
    obtain ⟨hu,hw⟩ := Finset.mem_product.mp hmem
    obtain ⟨i,hi,rfl⟩ := mem_vertices.mp hu
    obtain ⟨j,hj,rfl⟩ := mem_vertices.mp hw
    have hij : j = i+1 := by
      rcases hadj with ⟨c,hc⟩ | ⟨c,hc⟩
      · have hl := congrArg List.length hc
        simpa only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] using hl
      · have hl := congrArg List.length hc
        simp only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] at hl
        simp only [prefix_length_eq v hi, prefix_length_eq v hj] at hlt
        omega
    subst j
    exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro he
    obtain ⟨i,-,hei⟩ := Finset.mem_image.mp he
    rw [←hei]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩, ?_, ?_⟩
    · exact prefix_mem_vertices v (Nat.le_of_lt i.isLt)
    · exact prefix_mem_vertices v (Nat.succ_le_of_lt i.isLt)
    · exact prefix_adj v i.isLt
    · change (takeVertex v i.val).1.length < (takeVertex v (i.val+1)).1.length
      rw [prefix_length_eq v (Nat.le_of_lt i.isLt),
        prefix_length_eq v (Nat.succ_le_of_lt i.isLt)]
      omega

theorem freeCylinderWeight_vertices {d : ℕ} (theta : ℝ) (v : TreeVertex d)
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta (vertices v) eta = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ i : Fin v.1.length,
        transitionKernel theta (eta (path v i.castSucc)) (eta (path v i.succ))) := by
  classical
  rw [freeCylinderWeight_eq_transitionKernel, inducedEdges_vertices,
    Finset.prod_image]
  · rfl
  · exact fun _ _ _ _ h => pathEdge_injective v h

theorem path_cylinder_eq {d : ℕ} (v : TreeVertex d)
    (eta : Fin (v.1.length+1) → IsingSpin) :
    {x : TreeVertex d → IsingSpin | ∀ u ∈ vertices v, x u = pathAssignment v eta u} =
      {x | ∀ i : Fin (v.1.length+1), x (path v i) = eta i} := by
  classical
  ext x
  constructor
  · intro h i
    have hi : path v i ∈ vertices v :=
      prefix_mem_vertices v (Nat.le_of_lt_succ i.isLt)
    simpa only [pathAssignment_path] using h (path v i) hi
  · intro h u hu
    rw [vertices_eq_image_path] at hu
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hu
    simpa only [pathAssignment_path] using h i

theorem freeLaw_path_cylinder {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (v : TreeVertex d) (eta : Fin (v.1.length+1) → IsingSpin) :
    mu {x | ∀ i : Fin (v.1.length+1), x (path v i) = eta i} = ENNReal.ofReal
      ((1 / 2 : ℝ) * ∏ i : Fin v.1.length,
        transitionKernel theta (eta i.castSucc) (eta i.succ)) := by
  have h := hmu (vertices v) (connected_vertices v) (pathAssignment v eta)
  rw [path_cylinder_eq, freeCylinderWeight_vertices] at h
  simpa only [pathAssignment_path] using h

end ConnectedHull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootCorrelation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.root_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (v : TreeVertex d) :
    ∫ x, spinSign (x (ConnectedHull.root d)) * spinSign (x v) ∂mu =
      theta ^ v.1.length := by
  let := hmu.isProbabilityMeasure
  have h := integral_spinPath_of_cylinderLaw hlo hhi (ConnectedHull.path v)
    (fun eta => ConnectedHull.freeLaw_path_cylinder hmu v eta)
  simpa only [ConnectedHull.path, Fin.val_zero, Fin.val_last,
    ConnectedHull.prefix_zero, ConnectedHull.prefix_length] using h

theorem HasFreeIsingLaw.factor_root_correlation {d : ℕ} {theta : ℝ}
    {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}
    (hPhi : Measurable Phi) (hmu : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    ∫ U, spinSign (Phi U (ConnectedHull.root d)) * spinSign (Phi U v) ∂labelMeasure d =
      theta ^ v.1.length := by
  have hm : Measurable (fun x : TreeVertex d → IsingSpin =>
      spinSign (x (ConnectedHull.root d)) * spinSign (x v)) := by
    have hs : Measurable spinSign := measurable_spinToReal
    exact (hs.comp (measurable_pi_apply _)).mul (hs.comp (measurable_pi_apply _))
  exact (integral_map hPhi.aemeasurable hm.aestronglyMeasurable).symm.trans
    (hmu.root_correlation hlo hhi v)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_Observable
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanEquiv_apply_coe _root_.OAI.Problem367.ColoredEdgeLifts.centeredKoopmanIsometry_apply_coe _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordOperator_norm _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.FactorObservable

variable {d : ℕ}
variable {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}

lemma equivariant_field
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U)) :
    ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, field Phi (relabel g U) = relabel g (field Phi U) := by
  intro g
  filter_upwards [heq g] with U hU
  funext v
  exact congrArg IsingSpin.toReal (congrFun hU v)

lemma norm_spinLp (hPhi : Measurable Phi) (v : TreeVertex d) :
    ‖spinLp hPhi v‖ = 1 := by
  rw [spinLp, Lp.norm_toLp]
  have heq : eLpNorm (fun U => field Phi U v) 2 (labelMeasure d) =
      eLpNorm (fun _ : TreeVertex d → ℝ => (1 : ℝ)) 2 (labelMeasure d) := by
    apply eLpNorm_congr_norm_ae
    exact Filter.Eventually.of_forall (fun U => by
      change ‖(Phi U v).toReal‖ = ‖(1 : ℝ)‖
      rw [norm_spinToReal, norm_one])
  rw [heq, eLpNorm_const' _ (by norm_num) (by norm_num)]
  simp

@[simp] lemma norm_centeredSpinLp {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d))) (v : TreeVertex d) :
    ‖centeredSpinLp hPhi hlaw v‖ = 1 := norm_spinLp hPhi v

lemma inner_spinLp (hPhi : Measurable Phi) (u v : TreeVertex d) :
    inner ℝ (spinLp hPhi u) (spinLp hPhi v) =
      ∫ U, field Phi U u * field Phi U v ∂labelMeasure d := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_spinLp hPhi u, coe_spinLp hPhi v] with U hu hv
  rw [hu, hv]
  simp [mul_comm]

lemma inner_spinLp_root {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    inner ℝ (spinLp hPhi (ConnectedHull.root d)) (spinLp hPhi v) =
      theta ^ v.1.length := by
  rw [inner_spinLp]
  simpa only [field, IsingSpin.toReal_eq_spinSign] using
    hlaw.factor_root_correlation hPhi hlo hhi v

lemma inner_centeredSpinLp_root {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    inner ℝ (centeredSpinLp hPhi hlaw (ConnectedHull.root d))
      (centeredSpinLp hPhi hlaw v) = theta ^ v.1.length :=
  inner_spinLp_root hPhi hlaw hlo hhi v

end Problem367.FactorObservable

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_ObservableWord
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.FactorObservable

variable {d : ℕ}
variable {Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin)}

lemma wordOperator_spinLp_root (hPhi : Measurable Phi)
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U))
    (v : TreeVertex d) :
    RadialWalk.wordOperator TreeKoopman.generatorOperator v
      (spinLp hPhi (ConnectedHull.root d)) = spinLp hPhi v :=
  TreeKoopman.wordOperator_toLp_root (field Phi) (equivariant_field heq)
    (fun v => memLp_field hPhi v 2) v

lemma wordOperator_centeredSpinLp_root {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U))
    (v : TreeVertex d) :
    RadialWalk.wordOperator TreeKoopman.centeredGenerator v
      (centeredSpinLp hPhi hlaw (ConnectedHull.root d)) = centeredSpinLp hPhi hlaw v := by
  apply Subtype.ext
  rw [TreeKoopman.centered_wordOperator_apply_coe]
  exact wordOperator_spinLp_root hPhi heq v

lemma inner_centeredWordOperator_root {theta : ℝ} (hPhi : Measurable Phi)
    (hlaw : HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)))
    (heq : ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U))
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (v : TreeVertex d) :
    inner ℝ (centeredSpinLp hPhi hlaw (ConnectedHull.root d))
      (RadialWalk.wordOperator TreeKoopman.centeredGenerator v
        (centeredSpinLp hPhi hlaw (ConnectedHull.root d))) = theta ^ v.1.length := by
  rw [wordOperator_centeredSpinLp_root hPhi hlaw heq]
  exact inner_centeredSpinLp_root hPhi hlaw hlo hhi v

end Problem367.FactorObservable

namespace Problem367

theorem IsFactorOfIID.exists_centered_word_observable {d : ℕ} {theta : ℝ}
    (hfactor : IsFactorOfIID d theta) (hlo : -1 ≤ theta) (hhi : theta ≤ 1) :
    ∃ f : centeredL2 (labelMeasure d), ‖f‖ = 1 ∧
      ∀ v : TreeVertex d,
        inner ℝ f (RadialWalk.wordOperator TreeKoopman.centeredGenerator v f) =
          theta ^ v.1.length := by
  obtain ⟨Phi, hPhi, hlaw, heq⟩ := hfactor
  refine ⟨FactorObservable.centeredSpinLp hPhi hlaw (ConnectedHull.root d),
    FactorObservable.norm_centeredSpinLp hPhi hlaw _, ?_⟩
  intro v
  exact FactorObservable.inner_centeredWordOperator_root hPhi hlaw heq hlo hhi v

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_RadialPowerGrowth
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace RadialWalk

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_power_sq_eq_inner_double (A : H →L[ℝ] H)
    (hA : (A : H →ₗ[ℝ] H).IsSymmetric) (x : H) (n : ℕ) :
    ‖(A ^ n) x‖ ^ 2 = inner ℝ x ((A ^ (2 * n)) x) := by
  have hp : ((A ^ n : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric := by
    simpa only [ContinuousLinearMap.toLinearMap_pow] using hA.pow n
  calc
    ‖(A ^ n) x‖ ^ 2 = inner ℝ ((A ^ n) x) ((A ^ n) x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ x ((A ^ n) ((A ^ n) x)) := hp x ((A ^ n) x)
    _ = inner ℝ x ((A ^ (2 * n)) x) := by
      rw [show 2 * n = n + n by omega, pow_add]
      rfl

theorem norm_power_sq_le_of_radial_bound {d : ℕ}
    (S : Fin d → H →L[ℝ] H) (hS : ∀ c, S c * S c = 1)
    (hA : (operatorAverage S : H →ₗ[ℝ] H).IsSymmetric)
    (hd : 3 ≤ d) (x : H) {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ x (wordOperator S v x)| ≤ C * treeWeight d v)
    (n : ℕ) :
    ‖(operatorAverage S ^ n) x‖ ^ 2 ≤ C * rate d ^ (2 * n) := by
  rw [norm_power_sq_eq_inner_double _ hA]
  exact (le_abs_self _).trans (matrix_coefficient_power_bound S hS hd x hC hcov (2 * n))

theorem norm_power_le_of_radial_bound {d : ℕ}
    (S : Fin d → H →L[ℝ] H) (hS : ∀ c, S c * S c = 1)
    (hA : (operatorAverage S : H →ₗ[ℝ] H).IsSymmetric)
    (hd : 3 ≤ d) (x : H) {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ x (wordOperator S v x)| ≤ C * treeWeight d v)
    (n : ℕ) :
    ‖(operatorAverage S ^ n) x‖ ≤ Real.sqrt C * rate d ^ n := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (rate_nonneg d) n))).mp
  calc
    ‖(operatorAverage S ^ n) x‖ ^ 2 ≤ C * rate d ^ (2 * n) :=
      norm_power_sq_le_of_radial_bound S hS hA hd x hC hcov n
    _ = (Real.sqrt C * rate d ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC, ← pow_mul]
      rw [Nat.mul_comm n 2]

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_SpectralTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology
namespace Problem367
section
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

lemma selfAdjoint_pow_norm_sq_le (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (x : E) (n : ℕ) :
    ‖(T ^ n) x‖ ^ 2 ≤ ‖(T ^ (2 * n)) x‖ * ‖x‖ := by
  calc
    ‖(T ^ n) x‖ ^ 2 = RCLike.re (inner 𝕜 ((T ^ n) x) ((T ^ n) x)) :=
      (inner_self_eq_norm_sq _).symm
    _ = RCLike.re (inner 𝕜 ((T ^ n) ((T ^ n) x)) x) :=
      congrArg RCLike.re ((hT.pow n).isSymmetric ((T ^ n) x) x).symm
    _ = RCLike.re (inner 𝕜 ((T ^ (2 * n)) x) x) := by
      rw [two_mul, pow_add, mul_apply_eq_comp]
    _ ≤ ‖(T ^ (2 * n)) x‖ * ‖x‖ := re_inner_le_norm _ _

lemma selfAdjoint_norm_pow_two_pow_le (T : E →L[𝕜] E) (hT : IsSelfAdjoint T)
    (x : E) (hx : ‖x‖ = 1) (n : ℕ) :
    ‖T x‖ ^ (2 ^ n) ≤ ‖(T ^ (2 ^ n)) x‖ := by
  induction n with
  | zero => simp
  | succ n hn =>
    calc
      ‖T x‖ ^ (2 ^ (n + 1)) = (‖T x‖ ^ (2 ^ n)) ^ 2 := by
        rw [pow_succ, pow_mul]
      _ ≤ ‖(T ^ (2 ^ n)) x‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hn 2
      _ ≤ ‖(T ^ (2 * 2 ^ n)) x‖ := by
        simpa [hx] using selfAdjoint_pow_norm_sq_le T hT x (2 ^ n)
      _ = ‖(T ^ (2 ^ (n + 1))) x‖ := by rw [pow_succ, Nat.mul_comm]

lemma selfAdjoint_norm_apply_le_of_unit_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (x : E) (hx : ‖x‖ = 1)
    {rho C : ℝ} (hrho : 0 ≤ rho)
    (hbound : ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n) :
    ‖T x‖ ≤ rho := by
  rcases eq_or_lt_of_le hrho with hrho | hrho
  · simpa [← hrho] using hbound 1
  by_contra hnot
  have hratio : 1 < ‖T x‖ / rho := (one_lt_div hrho).2 (lt_of_not_ge hnot)
  have hlim : Tendsto (fun n : ℕ => (‖T x‖ / rho) ^ (2 ^ n)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hratio).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  obtain ⟨n, hn⟩ := (hlim.eventually_gt_atTop C).exists
  have hle : (‖T x‖ / rho) ^ (2 ^ n) ≤ C := by
    rw [div_pow, div_le_iff₀ (pow_pos hrho _)]
    exact (selfAdjoint_norm_pow_two_pow_le T hT x hx n).trans (hbound (2 ^ n))
  exact (not_lt_of_ge hle) hn

lemma selfAdjoint_norm_apply_le_of_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (x : E)
    {rho C : ℝ} (hrho : 0 ≤ rho)
    (hbound : ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n) :
    ‖T x‖ ≤ rho * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hi : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr (norm_nonneg x)
  let y : E := ((‖x‖⁻¹ : ℝ) : 𝕜) • x
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, inv_mul_cancel₀ hnx.ne']
  have hby (n : ℕ) : ‖(T ^ n) y‖ ≤ (‖x‖⁻¹ * C) * rho ^ n := by
    simpa [y, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hi, mul_assoc] using
      mul_le_mul_of_nonneg_left (hbound n) hi
  have h := selfAdjoint_norm_apply_le_of_unit_power_bound T hT y hy hrho hby
  have hdiv : ‖T x‖ / ‖x‖ ≤ rho := by
    simpa [y, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hi, div_eq_mul_inv, mul_comm]
      using h
  exact (div_le_iff₀ hnx).mp hdiv

lemma selfAdjoint_norm_apply_le_on_closure_of_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) {rho : ℝ} (hrho : 0 ≤ rho)
    {s : Set E}
    (hbound : ∀ x ∈ s, ∃ C : ℝ, ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n)
    {x : E} (hx : x ∈ closure s) : ‖T x‖ ≤ rho * ‖x‖ := by
  have hc : IsClosed {x : E | ‖T x‖ ≤ rho * ‖x‖} :=
    isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
  have hsub : s ⊆ {x : E | ‖T x‖ ≤ rho * ‖x‖} := by
    intro x hx
    obtain ⟨C, hC⟩ := hbound x hx
    exact selfAdjoint_norm_apply_le_of_power_bound T hT x hrho hC
  exact hc.closure_subset_iff.mpr hsub hx

lemma selfAdjoint_opNorm_le_of_dense_power_bound
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) {rho : ℝ} (hrho : 0 ≤ rho)
    {s : Set E} (hs : Dense s)
    (hbound : ∀ x ∈ s, ∃ C : ℝ, ∀ n : ℕ, ‖(T ^ n) x‖ ≤ C * rho ^ n) :
    ‖T‖ ≤ rho := by
  refine T.opNorm_le_bound hrho fun x => ?_
  exact selfAdjoint_norm_apply_le_on_closure_of_power_bound T hT hrho hbound
    (by rw [hs.closure_eq]; trivial)

end
end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BernoulliSpectral
attribute [-instance] _root_.OAI.Problem367.CopyDifference.rangeClosure_completeSpace _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.SpectralClosure.rangeClosure_completeSpace _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeKoopman

theorem local_average_power_bound {d : ℕ} (hd : 3 ≤ d)
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (labelMeasure d))
    (F : (s → ℝ) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[labelMeasure d] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂labelMeasure d) = 0) :
    ∃ C : ℝ, ∀ n : ℕ, ‖(average d ^ n) f‖ ≤ C * RadialWalk.rate d ^ n := by
  obtain ⟨C, hC, hcov⟩ := exists_local_koopman_critical_bound hd s f F hF hf hzero
  have hword (v : TreeVertex d) :
      |inner ℝ f (RadialWalk.wordOperator generatorOperator v f)| ≤
        C * RadialWalk.treeWeight d v := by
    have hdepth : ((wordAut v.1).symm.toEquiv TreeEscape.root).1.length =
        v.1.length := by
      change ((wordAut v.1).toEquiv.symm TreeEscape.root).1.length = _
      rw [TreeEscape.symm_root_depth]
      rw [wordAut_root v.1 v.2]
    simpa only [wordOperator_eq, wordRelabel, RadialWalk.treeWeight,
      RadialWalk.weight, hdepth] using hcov (wordAut v.1).symm
  have hsym : (RadialWalk.operatorAverage (generatorOperator (d := d)) :
      Lp ℝ 2 (labelMeasure d) →ₗ[ℝ] Lp ℝ 2 (labelMeasure d)).IsSymmetric := by
    rw [operatorAverage_eq]
    exact (average_selfAdjoint d).isSymmetric
  refine ⟨Real.sqrt C, fun n => ?_⟩
  simpa only [operatorAverage_eq] using
    RadialWalk.norm_power_le_of_radial_bound generatorOperator generatorOperator_sq
      hsym hd f hC hword n

theorem centeredAverage_norm_le {d : ℕ} (hd : 3 ≤ d) :
    ‖centeredAverage d‖ ≤ 2 * Real.sqrt ((d : ℝ) - 1) / d := by
  apply selfAdjoint_opNorm_le_of_dense_power_bound (centeredAverage d)
    (centeredAverage_selfAdjoint d) (RadialWalk.rate_nonneg d)
    (dense_centered_finite_coordinate (labelMeasure d))
  intro f hf
  obtain ⟨s, F, hF, hf⟩ := hf
  obtain ⟨C, hC⟩ := local_average_power_bound hd s (f : Lp ℝ 2 (labelMeasure d))
    F hF hf ((mem_centeredL2_iff _).mp f.property)
  refine ⟨C, fun n => ?_⟩
  change ‖((centeredAverage d ^ n) f : Lp ℝ 2 (labelMeasure d))‖ ≤ _
  rw [centeredAverage_pow_apply_coe]
  exact hC n

end Problem367.TreeKoopman

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_PowerObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

open Filter Topology

theorem le_one_of_pow_le_affine {q a c : ℝ}
    (h : ∀ n : ℕ, q ^ n ≤ a + c * (n : ℝ)) : q ≤ 1 := by
  by_contra hq
  have hq1 : 1 < q := lt_of_not_ge hq
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hconst : Tendsto (fun n : ℕ => a / q ^ n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_pow_const_div_const_pow_of_one_lt 0 hq1).const_mul a
  have hlinear : Tendsto (fun n : ℕ => c * ((n : ℝ) / q ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 1 hq1).const_mul c
  have hlim : Tendsto (fun n : ℕ => (a + c * (n : ℝ)) / q ^ n)
      atTop (𝓝 0) := by
    simpa [add_div, mul_div_assoc] using hconst.add hlinear
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim fun n => by
    exact (le_div_iff₀ (pow_pos hq0 n)).2 (by simpa using h n)
  exact (not_le_of_gt zero_lt_one) hfalse

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_WalkObstruction
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FactorObservable.norm_centeredSpinLp _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordOperator_norm _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace IsingWalk

theorem conjugateRoot_pos {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta) :
    0 < conjugateRoot b theta := by
  exact inv_pos.mpr (mul_pos hb ht)

theorem conjugateRoot_lt {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta)
    (hcritical : 1 < b * theta ^ 2) : conjugateRoot b theta < theta := by
  unfold conjugateRoot
  rw [inv_eq_one_div]
  apply (div_lt_iff₀ (mul_pos hb ht)).2
  nlinarith

theorem theta_le_eigenRate {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta)
    (ht1 : theta ≤ 1) : theta ≤ eigenRate b theta := by
  have hi : theta ≤ theta⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ ht).2
    nlinarith
  unfold eigenRate
  apply (le_div_iff₀ (by linarith : 0 < b + 1)).2
  nlinarith

theorem theta_characteristic {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta) :
    1 + b * theta ^ 2 = (b + 1) * eigenRate b theta * theta := by
  unfold eigenRate
  field_simp
  ring

theorem conjugate_characteristic {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta) :
    1 + b * conjugateRoot b theta ^ 2 =
      (b + 1) * eigenRate b theta * conjugateRoot b theta := by
  unfold conjugateRoot eigenRate
  field_simp

theorem eigenWeight_one (b theta : ℝ) :
    eigenWeight b theta 1 = eigenRate b theta * eigenWeight b theta 0 := by
  simp only [eigenWeight, pow_one, pow_zero]
  ring

theorem eigenWeight_recurrence {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta)
    (n : ℕ) :
    eigenWeight b theta n + b * eigenWeight b theta (n + 2) =
      (b + 1) * eigenRate b theta * eigenWeight b theta (n + 1) := by
  have h1 := theta_characteristic hb ht
  have h2 := conjugate_characteristic hb ht
  unfold eigenWeight
  simp only [pow_add, pow_one, pow_two]
  linear_combination
    (eigenRate b theta - conjugateRoot b theta) * theta ^ n * h1 -
    (eigenRate b theta - theta) * conjugateRoot b theta ^ n * h2

theorem eigenWeight_le {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (n : ℕ) :
    eigenWeight b theta n ≤ (eigenRate b theta - conjugateRoot b theta) * theta ^ n := by
  unfold eigenWeight
  have := mul_nonneg (sub_nonneg.mpr (theta_le_eigenRate hb ht ht1))
    (pow_nonneg (conjugateRoot_pos hb ht).le n)
  linarith

theorem critical_square_lt {b theta : ℝ} (hb : 0 < b)
    (ht : 1 / Real.sqrt b < theta) : 1 < b * theta ^ 2 := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hp : 1 < theta * Real.sqrt b := (div_lt_iff₀ hs).mp ht
  have he : (theta * Real.sqrt b) ^ 2 = b * theta ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb.le]
    ring
  nlinarith

theorem eigenRate_gt_critical {b theta : ℝ} (hb : 0 < b)
    (ht : 1 / Real.sqrt b < theta) :
    2 * Real.sqrt b / (b + 1) < eigenRate b theta := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have ht0 : 0 < theta := lt_trans (one_div_pos.mpr hs) ht
  have hp : 1 < theta * Real.sqrt b := (div_lt_iff₀ hs).mp ht
  have hsq : 0 < (theta * Real.sqrt b - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have he : (theta * Real.sqrt b) ^ 2 = b * theta ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb.le]
    ring
  have hc := theta_characteristic hb ht0
  apply (div_lt_iff₀ (by linarith : 0 < b + 1)).2
  nlinarith

theorem average_treeEigenWeight {d : ℕ} (hd : 3 ≤ d) {theta : ℝ} (ht : 0 < theta)
    (v : TreeVertex d) :
    RadialWalk.average treeStep (treeEigenWeight d theta) v =
      eigenRate ((d : ℝ) - 1) theta * treeEigenWeight d theta v := by
  classical
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hsum := sum_treeNeighborFinset_radial v (eigenWeight ((d : ℝ) - 1) theta)
  rw [treeNeighborFinset, Finset.sum_image (treeStep_injective v).injOn] at hsum
  unfold RadialWalk.average treeEigenWeight
  rw [hsum]
  by_cases hv : v.1.length = 0
  · rw [ite_eq_left hv, hv]
    rw [mul_div_cancel_left₀ _ hd0]
    exact eigenWeight_one _ _
  · rw [ite_eq_right hv]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hv
    rw [hn]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    apply (div_eq_iff hd0).2
    have hr := eigenWeight_recurrence hb ht n
    convert hr using 1
    all_goals try with_reducible_and_instances rfl
    ring

theorem iterate_eigenfunction {V : Type*} {d : ℕ} (step : V → Fin d → V)
    (q : V → ℝ) (lambda : ℝ)
    (hq : ∀ v, RadialWalk.average step q v = lambda * q v) (n : ℕ) :
    ∀ v, ((RadialWalk.average step)^[n]) q v = lambda ^ n * q v := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [Function.iterate_succ_apply']
    have hi : ((RadialWalk.average step)^[n]) q = fun w => lambda ^ n * q w := funext ih
    rw [hi, RadialWalk.average_mul, hq, pow_succ]
    ring

theorem ising_walk_lower_bound {d : ℕ} (hd : 3 ≤ d) {theta : ℝ}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (n : ℕ)
    (o : TreeVertex d) (ho : o.1.length = 0) :
    eigenRate ((d : ℝ) - 1) theta ^ n *
        (theta - conjugateRoot ((d : ℝ) - 1) theta) ≤
      (eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta) *
        ((RadialWalk.average treeStep)^[n]) (fun v : TreeVertex d => theta ^ v.1.length) o := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hle := RadialWalk.iterate_average_mono treeStep
    (fun v : TreeVertex d => eigenWeight_le hb ht ht1 v.1.length) n o
  have he := iterate_eigenfunction treeStep (treeEigenWeight d theta)
    (eigenRate ((d : ℝ) - 1) theta) (average_treeEigenWeight hd ht) n o
  change ((RadialWalk.average treeStep)^[n]) (treeEigenWeight d theta) o ≤ _ at hle
  rw [he, RadialWalk.iterate_average_mul] at hle
  simpa only [treeEigenWeight, ho, eigenWeight_zero] using hle

theorem le_of_exponential_bound {a b delta K : ℝ} (hb : 0 < b) (hd : 0 < delta)
    (h : ∀ n : ℕ, a ^ n * delta ≤ K * b ^ n) : a ≤ b := by
  have hq : a / b ≤ 1 := le_one_of_pow_le_affine (a := K / delta) (c := 0) (by
    intro n
    simp only [zero_mul, add_zero, div_pow]
    apply (div_le_iff₀ (pow_pos hb n)).2
    calc
      a ^ n ≤ (K * b ^ n) / delta := (le_div_iff₀ hd).2 (h n)
      _ = K / delta * b ^ n := by ring)
  exact (div_le_one hb).mp hq

theorem threshold_of_ising_walk_bound {d : ℕ} (hd : 3 ≤ d) {theta : ℝ}
    (ht1 : theta ≤ 1) (o : TreeVertex d) (ho : o.1.length = 0)
    (C : ℝ)
    (hbound : ∀ n : ℕ,
      ((RadialWalk.average treeStep)^[n]) (fun v : TreeVertex d => theta ^ v.1.length) o ≤
        C * RadialWalk.rate d ^ n) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  by_contra hnot
  have hcritical : 1 / Real.sqrt ((d : ℝ) - 1) < theta := lt_of_not_ge hnot
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hb
  have ht : 0 < theta := (one_div_pos.mpr hs).trans hcritical
  have hr : conjugateRoot ((d : ℝ) - 1) theta < theta :=
    conjugateRoot_lt hb ht (critical_square_lt hb hcritical)
  have hdelta : 0 < theta - conjugateRoot ((d : ℝ) - 1) theta := sub_pos.mpr hr
  have hA : 0 < eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta := by
    have := theta_le_eigenRate hb ht ht1
    linarith
  have hrho : 0 < RadialWalk.rate d := by
    unfold RadialWalk.rate
    positivity
  have hlarge : RadialWalk.rate d < eigenRate ((d : ℝ) - 1) theta := by
    simpa only [RadialWalk.rate, sub_add_cancel] using eigenRate_gt_critical hb hcritical
  apply (not_le_of_gt hlarge)
  apply le_of_exponential_bound hrho hdelta
    (K := (eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta) * C)
  intro n
  calc
    eigenRate ((d : ℝ) - 1) theta ^ n *
        (theta - conjugateRoot ((d : ℝ) - 1) theta) ≤
        (eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta) *
          ((RadialWalk.average treeStep)^[n])
            (fun v : TreeVertex d => theta ^ v.1.length) o :=
      ising_walk_lower_bound hd ht ht1 n o ho
    _ ≤ (eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta) *
        (C * RadialWalk.rate d ^ n) := mul_le_mul_of_nonneg_left (hbound n) hA.le
    _ = _ := by ring

theorem threshold_of_operatorAverage_norm {d : ℕ} (hd : 3 ≤ d) {theta : ℝ}
    (ht1 : theta ≤ 1) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : Fin d → H →L[ℝ] H) (hS : ∀ c, S c * S c = 1) (x : H)
    (hnorm : ‖RadialWalk.operatorAverage S‖ ≤ RadialWalk.rate d)
    (hcov : ∀ v : TreeVertex d,
      inner ℝ x (RadialWalk.wordOperator S v x) = theta ^ v.1.length) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  let o : TreeVertex d := ⟨[], List.IsChain.nil⟩
  have hxx : inner ℝ x x = 1 := by
    simpa [RadialWalk.wordOperator, o] using hcov o
  have hx0 : x ≠ 0 := by
    intro hx
    simp [hx] at hxx
  let : Nontrivial H := ⟨⟨x, 0, hx0⟩⟩
  apply threshold_of_ising_walk_bound hd ht1 o rfl (‖x‖ ^ 2)
  intro n
  have hi := congrFun (RadialWalk.inner_iterate_vectorAverage treeStep x
    (fun v => RadialWalk.wordOperator S v x) n) o
  rw [RadialWalk.iterate_vectorAverage_wordOperator S hS] at hi
  have hc : (fun v : TreeVertex d => inner ℝ x (RadialWalk.wordOperator S v x)) =
      (fun v : TreeVertex d => theta ^ v.1.length) := funext hcov
  rw [hc] at hi
  simp only [RadialWalk.wordOperator, o, List.map_nil, List.prod_nil,
    one_apply_eq_self] at hi
  rw [← hi]
  calc
    inner ℝ x ((RadialWalk.operatorAverage S ^ n) x) ≤
        ‖x‖ * ‖(RadialWalk.operatorAverage S ^ n) x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖RadialWalk.operatorAverage S ^ n‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖x‖ * (‖RadialWalk.operatorAverage S‖ ^ n * ‖x‖) := by
      gcongr
      exact norm_pow_le _ _
    _ ≤ ‖x‖ * (RadialWalk.rate d ^ n * ‖x‖) := by
      gcongr
    _ = ‖x‖ ^ 2 * RadialWalk.rate d ^ n := by ring

end IsingWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_Necessity
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem IsFactorOfIID.threshold_of_centeredAverage_norm {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (hfactor : IsFactorOfIID d theta)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (hnorm : ‖TreeKoopman.centeredAverage d‖ ≤ RadialWalk.rate d) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  obtain ⟨f, _, hcov⟩ := hfactor.exists_centered_word_observable hlo hhi
  apply IsingWalk.threshold_of_operatorAverage_norm hd hhi
    TreeKoopman.centeredGenerator TreeKoopman.centeredGenerator_sq f
  · simpa only [TreeKoopman.centered_operatorAverage_eq] using hnorm
  · exact hcov

theorem IsFactorOfIID.le_threshold {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (hfactor : IsFactorOfIID d theta)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  apply hfactor.threshold_of_centeredAverage_norm hd hlo hhi
  exact TreeKoopman.centeredAverage_norm_le hd

theorem free_ising_factor_only_if_threshold (d : ℕ) (beta : ℝ)
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hfactor : IsFactorOfIID d (Real.tanh beta)) :
    Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  apply hfactor.le_threshold hd
  · exact le_trans (by norm_num) (tanh_nonneg_of_beta_nonneg hbeta)
  · exact (Real.tanh_lt_one beta).le

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FreeIsingBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem free_ising_factor_below_threshold :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta → Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) → IsFactorOfIID d (Real.tanh beta) := by
  apply free_ising_factor_below_threshold_of_actual_variance_identity
  intro d beta hd hb hcrit T
  exact IsingObservationFactor.actual_variance_analysis hd
    (freeIsingMeasure_hasFreeIsingLaw d (Real.neg_one_lt_tanh beta).le
      (Real.tanh_lt_one beta).le) hb.le hcrit T

theorem free_ising_factor_iff_threshold_oai :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta → (IsFactorOfIID d (Real.tanh beta) ↔ Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) := by
  intro d beta hd hbeta
  exact ⟨free_ising_factor_only_if_threshold d beta hd hbeta,
    free_ising_factor_below_threshold d beta hd hbeta⟩

end Problem367

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.free_ising_factor_iff_threshold_oai := @OAI.Problem367.free_ising_factor_iff_threshold_oai
