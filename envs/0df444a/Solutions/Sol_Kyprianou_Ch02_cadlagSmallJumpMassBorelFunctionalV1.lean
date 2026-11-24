-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagSmallJumpMassBorelFunctionalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:42:45.191266+00:00
-- url     : https://prove2.me/submissions/bdcec6b5-34a9-4abd-ade9-9bdb41aec913

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_cadlag_true_mark_measurable
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reuse the measurable marked jump functional for truncated absolute weights. -/
theorem solution
    (T : ℝ≥0) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ (Y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt Y (Set.Ici t) t) →
        (∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ, Tendsto Y (𝓝[<] t) (𝓝 l)) →
        F Y = ∑' s : Set.Ioc (0 : ℝ≥0) T,
          ENNReal.ofReal
            (if |Y (s : ℝ≥0) -
                 Function.leftLim Y (s : ℝ≥0)| ≤ (1 : ℝ)
             then |Y (s : ℝ≥0) -
                    Function.leftLim Y (s : ℝ≥0)|
             else 0) := by
  classical
  let g : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (if |z| ≤ (1 : ℝ) then |z| else 0)
  have hg : Measurable g :=
    ENNReal.measurable_ofReal.comp
      (Measurable.ite (measurableSet_le measurable_abs measurable_const)
        measurable_abs measurable_const)
  obtain ⟨F, hF, hrep⟩ :=
    AvramDividend.Classical.avram_bv_jump8_cadlag_mark_weight_lintegral_borel T g hg
  refine ⟨F, hF, ?_⟩
  intro Y hR hL
  let j : ℝ≥0 → ℝ := fun u => Y u - Function.leftLim Y u
  have hm :=
    AvramDividend.Classical.avram_bv_jump8_turn9_cadlag_true_mark_measurable Y hR hL
  let f : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0
  have hfst : Measurable (Prod.fst : ℝ≥0 × ℝ → ℝ≥0) := measurable_fst
  have hwindow : MeasurableSet {p : ℝ≥0 × ℝ | 0 < p.1 ∧ p.1 ≤ T} :=
    (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ≥0) T)).preimage hfst
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
  have hg0 : g 0 = 0 := by simp [g]
  by_cases hpos : 0 < u <;> by_cases hT : u ≤ T <;> by_cases hj : j u = 0 <;>
    simp [Set.indicator, Set.mem_Ioc, f, hpos, hT, hj, hg0]
