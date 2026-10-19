-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.averaged_scale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:57:08.997648+00:00
-- url     : https://prove2.me/submissions/07ffda0f-300c-456d-8424-8d80fcf7d2b9

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h44_ment_inj {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℤ)
    (h : ℤ → ℤ) (hinj : Function.Injective h) : entropy μ (h ∘ f) = entropy μ f := by
  unfold entropy
  rw [← hinj.tsum_eq]
  · congr 1
    ext b
    congr 1
    unfold mass
    congr 1
    ext x
    exact hinj.eq_iff
  · intro c hc
    by_contra hr
    apply hc
    show Real.negMulLog (mass μ (h ∘ f) c) = 0
    have : {x | (h ∘ f) x = c} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Function.comp_apply]
      exact fun hx => hr ⟨f x, hx⟩
    unfold mass
    rw [this]
    simp

theorem h44_grid_per (μ : Measure ℝ) (s : ℝ) : Function.Periodic (grid μ s) 1 := by
  intro u
  unfold grid
  have : label s (u + 1) = (fun j => j + 1) ∘ label s u := by
    funext x
    simp only [label, Function.comp_apply]
    rw [← add_assoc, Int.floor_add_one]
  rw [this, h44_ment_inj μ _ _ (fun a b h => by simpa using h)]

theorem h44_ent_map (μ : Measure ℝ) {T : ℝ → ℝ} (hT : Measurable T) {f : ℝ → ℤ}
    (hf : Measurable f) : entropy (μ.map T) f = entropy μ (f ∘ T) := by
  unfold entropy
  congr 1
  ext b
  congr 1
  unfold mass
  simp only [Measure.real_def]
  rw [Measure.map_apply (s := {x | f x = b}) hT (hf (measurableSet_singleton b))]
  rfl

theorem h44_ment_ae (μ : Measure ℝ) {f g : ℝ → ℤ} (h : f =ᵐ[μ] g) :
    entropy μ f = entropy μ g := by
  unfold entropy
  congr 1
  ext b
  congr 1
  unfold mass
  simp only [Measure.real_def]
  congr 1
  apply measure_congr
  filter_upwards [h] with x hx
  change (f x = b) = (g x = b)
  rw [hx]

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s a : ℝ} (hs : 0 < s) (ha : a ≠ 0) :
    averaged (μ.map (fun x => a*x)) s = averaged μ (s/|a|) := by
  have hT : Measurable (fun x : ℝ => a * x) := by fun_prop
  have hc : 0 < |a| := abs_pos.mpr ha
  have hs' : 0 < s / |a| := div_pos hs hc
  have hgm : ∀ u, grid (μ.map (fun x => a*x)) s u = entropy μ (label s u ∘ (fun x => a*x)) :=
    fun u => h44_ent_map μ hT (label_measurable s u)
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have habs : |a| = -a := abs_of_neg hneg
    set s' := s / |a| with hs'def
    have hlab : ∀ u, label s u ∘ (fun x => a*x) = (fun j : ℤ => -j) ∘ (fun x => ⌈x/s' - u⌉) := by
      intro u
      funext x
      simp only [label, Function.comp_apply]
      rw [← Int.floor_neg]
      congr 1
      rw [hs'def, habs]
      field_simp
      ring
    -- countably many bad offsets
    have hA : Set.Countable {x : ℝ | 0 < μ ({x} : Set ℝ)} :=
      Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top μ
        (fun x => measurableSet_singleton x)
        (fun x y hxy => Set.disjoint_singleton.mpr hxy) (measure_ne_top _ _)
    set U : Set ℝ := ⋃ k : ℤ, (fun x => x/s' - k) '' {x : ℝ | 0 < μ ({x} : Set ℝ)} with hU
    have hUc : U.Countable := Set.countable_iUnion (fun k => hA.image _)
    have hUn : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ U :=
      (measure_eq_zero_iff_ae_notMem).mp (hUc.measure_zero _)
    have hgood : ∀ u, u ∉ U → grid (μ.map (fun x => a*x)) s u = grid μ s' (-u) := by
      intro u hu
      rw [hgm, hlab, h44_ment_inj μ _ _ (fun a b h => by simpa using h)]
      have hae : (fun x => ⌈x/s' - u⌉) =ᵐ[μ] (fun j : ℤ => j + 1) ∘ label s' (-u) := by
        have hnull : μ {x | ∃ k : ℤ, x/s' - u = k} = 0 := by
          have he : {x | ∃ k : ℤ, x/s' - u = k} = ⋃ k : ℤ, {x | x/s' - u = k} := by
            ext x; simp
          rw [he]
          apply measure_iUnion_null
          intro k
          have hsub : {x | x/s' - u = (k : ℝ)} ⊆ {s' * (k + u)} := by
            intro x hx
            simp only [Set.mem_setOf_eq] at hx
            simp only [Set.mem_singleton_iff]
            field_simp at hx
            linarith
          apply measure_mono_null hsub
          by_contra hpos'
          apply hu
          rw [hU, Set.mem_iUnion]
          refine ⟨k, s' * (k + u), pos_iff_ne_zero.mpr hpos', ?_⟩
          field_simp
          ring
        rw [Filter.EventuallyEq, ae_iff]
        apply measure_mono_null _ hnull
        intro x hx
        simp only [Set.mem_setOf_eq, Function.comp_apply, label] at hx ⊢
        by_contra hk
        apply hx
        have : x/s' - u ∉ Set.range (Int.cast : ℤ → ℝ) := by
          rintro ⟨k, hk'⟩
          exact hk ⟨k, hk'.symm⟩
        rw [(Int.ceil_eq_floor_add_one_iff_notMem _).mpr this, sub_eq_add_neg]
      rw [h44_ment_ae μ hae, h44_ment_inj μ _ _ (fun a b h => by simpa using h)]
      rfl
    unfold averaged
    rw [setIntegral_congr_ae measurableSet_Icc (hUn.mono fun u hu _ => hgood u hu),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_neg (fun u => grid μ s' u)]
    have := (h44_grid_per μ s').intervalIntegral_add_eq (-1) 0
    norm_num at this
    rw [neg_zero]
    exact this
  · unfold averaged
    refine setIntegral_congr_fun measurableSet_Icc (fun u _ => ?_)
    rw [hgm]
    unfold grid
    congr 1
    funext x
    simp only [label, Function.comp_apply, abs_of_pos hpos]
    congr 1
    field_simp

