-- Prove2me | solution 1 for MFEUnique.Uniq.stochLE_iff_upper_set
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:25:05.709985+00:00
-- url     : https://prove2.me/submissions/d6a5b3d9-e9d3-4f8d-9c6f-df45a79cb0a8

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

end MFEUAux

open MFEUAux

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    (s₁ s₂ : ProbabilityMeasure X) :
    StochLE (s₂ : Measure X) (s₁ : Measure X) ↔
      ∀ B : Set X, MeasurableSet B → IsUpperSet B → (s₂ : Measure X) B ≤ (s₁ : Measure X) B := by
  constructor
  · intro h B hB hU
    exact upper_le_of_stochLE h hB hU
  · intro h
    exact stochLE_of_upper fun F hF hU => h F hF.measurableSet hU
