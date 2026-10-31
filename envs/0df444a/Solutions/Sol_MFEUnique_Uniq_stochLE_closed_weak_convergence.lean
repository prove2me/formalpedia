-- Prove2me | solution 1 for MFEUnique.Uniq.stochLE_closed_weak_convergence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:25:06.520062+00:00
-- url     : https://prove2.me/submissions/f8b4b19e-b538-45af-9867-eb4a136fe655

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium

open MeasureTheory StochIneqPO.Comparison Filter Topology
open MFEUnique.Uniq

namespace MFEUAux

variable {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]

lemma isClosed_upperClosure_of_isClosed {F : Set X} (hF : IsClosed F) :
    IsClosed (upperClosure F : Set X) := by
  have hK : IsCompact ({p : X × X | p.1 ≤ p.2} ∩ F ×ˢ Set.univ) :=
    (hF.prod isClosed_univ).isCompact.inter_left (isClosed_le continuous_fst continuous_snd)
  have : (upperClosure F : Set X) = Prod.snd '' ({p : X × X | p.1 ≤ p.2} ∩ F ×ˢ Set.univ) := by
    ext y
    rw [SetLike.mem_coe, mem_upperClosure]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx, Set.mem_univ _⟩, rfl⟩
    · rintro ⟨⟨x, y'⟩, ⟨hxy, hx, -⟩, rfl⟩
      exact ⟨x, hx, hxy⟩
  rw [this]
  exact (hK.image continuous_snd).isClosed

lemma le_of_null_upper {ν μ : Measure X} [IsFiniteMeasure ν]
    (h : ∀ F : Set X, IsClosed F → IsUpperSet F → ν F ≤ μ F)
    {U : Set X} (hU : IsUpperSet U) (hUm : NullMeasurableSet U ν) : ν U ≤ μ U := by
  obtain ⟨t, htU, htm, hae⟩ := hUm.exists_measurable_subset_ae_eq
  rw [← measure_congr hae]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨F, hFt, hFc, hlt⟩ := htm.exists_isClosed_lt_add (μ := ν) (measure_ne_top ν t)
    (ε := (ε : ENNReal)) (by exact_mod_cast hε.ne')
  have hsub : (upperClosure F : Set X) ⊆ U := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := mem_upperClosure.1 hy
    exact hU hxy (htU (hFt hx))
  calc ν t ≤ ν F + ε := hlt.le
    _ ≤ ν (upperClosure F) + ε := by gcongr; exact subset_upperClosure
    _ ≤ μ (upperClosure F) + ε :=
        add_le_add (h _ (isClosed_upperClosure_of_isClosed hFc) (upperClosure F).upper) le_rfl
    _ ≤ μ U + ε := by gcongr

lemma lintegral_le_of_upper {ν μ : Measure X} [IsFiniteMeasure ν]
    (h : ∀ F : Set X, IsClosed F → IsUpperSet F → ν F ≤ μ F)
    {f : X → ℝ} (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x)
    (hν : AEMeasurable f ν) (hμ : AEMeasurable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  rw [lintegral_eq_lintegral_meas_lt ν (Filter.Eventually.of_forall hf0) hν,
    lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hf0) hμ]
  refine lintegral_mono fun t => ?_
  refine le_of_null_upper h ?_ (nullMeasurableSet_lt aemeasurable_const hν)
  intro a b hab ha
  exact lt_of_lt_of_le ha (hf hab)

lemma stochLE_of_upper {ν μ : Measure X} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (h : ∀ F : Set X, IsClosed F → IsUpperSet F → ν F ≤ μ F) : StochLE ν μ := by
  intro f hfm hfmono ⟨C, hC⟩
  set D := |C|
  have hfD : ∀ x, 0 ≤ f x + D := fun x => by
    have := hC x
    have := le_abs_self C
    have := neg_abs_le (f x)
    linarith
  have hint : ∀ (m : Measure X) [IsFiniteMeasure m], Integrable f m := fun m _ =>
    Integrable.of_bound hfm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have key : ∫ x, (f x + D) ∂ν ≤ ∫ x, (f x + D) ∂μ := by
    have h1 := ofReal_integral_eq_lintegral_ofReal ((hint ν).add (integrable_const D))
      (Filter.Eventually.of_forall hfD)
    have h2 := ofReal_integral_eq_lintegral_ofReal ((hint μ).add (integrable_const D))
      (Filter.Eventually.of_forall hfD)
    have h3 := lintegral_le_of_upper h (f := fun x => f x + D)
      (fun a b hab => by simpa using hfmono hab) hfD
      (hfm.add measurable_const).aemeasurable (hfm.add measurable_const).aemeasurable
    simp only [Pi.add_apply] at h1 h2
    rw [← h1, ← h2] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hfD)).1 h3
  rw [integral_add (hint ν) (integrable_const D), integral_add (hint μ) (integrable_const D)]
    at key
  simp only [integral_const, probReal_univ, one_smul] at key
  linarith

lemma upper_le_of_stochLE {ν μ : Measure X} [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (h : StochLE ν μ) {B : Set X} (hB : MeasurableSet B) (hU : IsUpperSet B) : ν B ≤ μ B := by
  have hmono : Monotone (B.indicator (1 : X → ℝ)) := by
    intro a b hab
    by_cases ha : a ∈ B
    · simp [Set.indicator_of_mem ha, Set.indicator_of_mem (hU hab ha)]
    · rw [Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) b
  have := h (B.indicator 1) (measurable_one.indicator hB) hmono
    ⟨1, fun x => by by_cases hx : x ∈ B <;> simp [hx]⟩
  rw [integral_indicator_one hB, integral_indicator_one hB] at this
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 this

lemma isClosed_lowerClosure_of_isClosed {F : Set X} (hF : IsClosed F) :
    IsClosed (lowerClosure F : Set X) := by
  have hK : IsCompact ({p : X × X | p.2 ≤ p.1} ∩ F ×ˢ Set.univ) :=
    (hF.prod isClosed_univ).isCompact.inter_left (isClosed_le continuous_snd continuous_fst)
  have : (lowerClosure F : Set X) = Prod.snd '' ({p : X × X | p.2 ≤ p.1} ∩ F ×ˢ Set.univ) := by
    ext y
    rw [SetLike.mem_coe, mem_lowerClosure]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx, Set.mem_univ _⟩, rfl⟩
    · rintro ⟨⟨x, y'⟩, ⟨hxy, hx, -⟩, rfl⟩
      exact ⟨x, hx, hxy⟩
  rw [this]
  exact (hK.image continuous_snd).isClosed

end MFEUAux

open MFEUAux

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X]
    [PartialOrder X] [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    (μn νn : ℕ → Measure X) (hμn : ∀ n, IsProbabilityMeasure (μn n))
    (hνn : ∀ n, IsProbabilityMeasure (νn n)) (μ ν : ProbabilityMeasure X)
    (hμ : WeakConv μn (μ : Measure X)) (hν : WeakConv νn (ν : Measure X))
    (h : ∀ n, StochLE (νn n) (μn n)) :
    StochLE (ν : Measure X) (μ : Measure X) := by
  let μs : ℕ → ProbabilityMeasure X := fun n => ⟨μn n, hμn n⟩
  let νs : ℕ → ProbabilityMeasure X := fun n => ⟨νn n, hνn n⟩
  have hμt : Tendsto μs atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    exact fun f => hμ f
  have hνt : Tendsto νs atTop (𝓝 ν) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    exact fun f => hν f
  refine stochLE_of_upper fun F hF hU => ?_
  -- for `r > 0`, an open upper set `U` with `F ⊆ U ⊆ thickening r F`
  have hr : ∀ r : ℝ, 0 < r → (ν : Measure X) F ≤ (μ : Measure X) (Metric.cthickening r F) := by
    intro r hr
    set L : Set X := (lowerClosure (Metric.thickening r F)ᶜ : Set X) with hL
    have hLc : IsClosed L :=
      isClosed_lowerClosure_of_isClosed Metric.isOpen_thickening.isClosed_compl
    set U : Set X := Lᶜ
    have hUo : IsOpen U := hLc.isOpen_compl
    have hUu : IsUpperSet U := (lowerClosure (Metric.thickening r F)ᶜ).lower.compl
    have hFU : F ⊆ U := by
      intro x hx hxL
      obtain ⟨y, hy, hxy⟩ := mem_lowerClosure.1 hxL
      exact hy (Metric.self_subset_thickening hr F (hU hxy hx))
    have hUT : U ⊆ Metric.thickening r F := by
      intro x hx
      by_contra hxT
      exact hx (subset_lowerClosure hxT)
    have hcl : closure U ⊆ Metric.cthickening r F :=
      (closure_mono hUT).trans (Metric.closure_thickening_subset_cthickening r F)
    calc (ν : Measure X) F ≤ (ν : Measure X) U := measure_mono hFU
      _ ≤ liminf (fun n => (νs n : Measure X) U) atTop :=
          ProbabilityMeasure.le_liminf_measure_open_of_tendsto hνt hUo
      _ ≤ liminf (fun n => (μs n : Measure X) U) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n =>
            upper_le_of_stochLE (h n) hUo.measurableSet hUu)
      _ ≤ limsup (fun n => (μs n : Measure X) U) atTop := liminf_le_limsup
      _ ≤ limsup (fun n => (μs n : Measure X) (closure U)) atTop :=
          limsup_le_limsup (Eventually.of_forall fun n => measure_mono subset_closure)
      _ ≤ (μ : Measure X) (closure U) :=
          ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμt isClosed_closure
      _ ≤ (μ : Measure X) (Metric.cthickening r F) := measure_mono hcl
  have ht : Tendsto (fun r => (μ : Measure X) (Metric.cthickening r F)) (𝓝[>] 0)
      (𝓝 ((μ : Measure X) F)) :=
    (tendsto_measure_cthickening_of_isClosed ⟨1, one_pos, measure_ne_top _ _⟩ hF).mono_left
      nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun r hr' => hr r hr')
