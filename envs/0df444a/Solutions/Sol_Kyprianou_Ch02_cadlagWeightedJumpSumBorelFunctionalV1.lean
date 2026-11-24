-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagWeightedJumpSumBorelFunctionalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:14:00.697442+00:00
-- url     : https://prove2.me/submissions/e51b5b53-11e0-4d6e-b851-fb8d705427f3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_cadlag_true_mark_measurable
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Measurable weighted sum over actual positive-time jumps. -/
theorem solution
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) (hg0 : g 0 = 0) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ t : ℝ≥0, ContinuousWithinAt Y (Set.Ici t) t) →
        (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto Y (𝓝[<] t) (𝓝 l)) →
        F Y = ∑' s : Set.Ioc (0 : ℝ≥0) T,
          g (Y (s : ℝ≥0) - Function.leftLim Y (s : ℝ≥0)) := by
  classical
  obtain ⟨F, hF, hrep⟩ :=
    AvramDividend.Classical.avram_bv_jump8_cadlag_mark_weight_lintegral_borel T g hg
  refine ⟨F, hF, ?_⟩
  intro Y hR hL
  let j : ℝ≥0 → ℝ := fun u => Y u - Function.leftLim Y u
  have hm :=
    AvramDividend.Classical.avram_bv_jump8_turn9_cadlag_true_mark_measurable Y hR hL
  let f : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0
  have hwindow : MeasurableSet {p : ℝ≥0 × ℝ | 0 < p.1 ∧ p.1 ≤ T} :=
    (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ≥0) T)).preimage measurable_fst
  have hf : Measurable f :=
    Measurable.ite hwindow (hg.comp measurable_snd) measurable_const
  rw [hrep Y hR hL]
  change (∫⁻ p, f p ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u => (u, j u)))) = ∑' s : Ioc (0 : ℝ≥0) T, g (j s)
  rw [lintegral_map hf hm.1]
  rw [← lintegral_indicator hm.2 (fun u : ℝ≥0 => f (u, j u))]
  rw [lintegral_count, tsum_subtype (Ioc (0 : ℝ≥0) T) (fun u => g (j u))]
  apply tsum_congr
  intro u
  change {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}.indicator (fun u => f (u, j u)) u =
    (Ioc (0 : ℝ≥0) T).indicator (fun u => g (j u)) u
  by_cases hpos : 0 < u <;> by_cases hT : u ≤ T <;> by_cases hj : j u = 0 <;>
    simp [Set.indicator, Set.mem_Ioc, f, hpos, hT, hj, hg0]
