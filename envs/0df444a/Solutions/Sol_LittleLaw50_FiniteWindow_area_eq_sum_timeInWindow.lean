-- Prove2me | solution 1 for LittleLaw50.FiniteWindow.area_eq_sum_timeInWindow
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:27:49.807239+00:00
-- url     : https://prove2.me/submissions/9df03b6f-f517-4815-a7f2-20ec465b595a

import Mathlib
import Definitions.Def_LittleLaw50_FiniteWindow_Window

open MeasureTheory Set
open LittleLaw50.FiniteWindow

private lemma indicator_area (a d T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, Set.indicator (Set.Ico a d) (fun _ => (1 : ℝ)) t) =
      max 0 (min d T - max a 0) := by
  rw [intervalIntegral.integral_of_le hT,
    MeasureTheory.integral_indicator measurableSet_Ico,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ico]
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
  have h₁ : Ioo (max a 0) (min d T) ⊆ Ico a d ∩ Ioc 0 T := by
    intro x hx
    exact ⟨⟨(le_max_left a 0).trans hx.1.le, hx.2.trans_le (min_le_left d T)⟩,
      ⟨(le_max_right a 0).trans_lt hx.1, hx.2.le.trans (min_le_right d T)⟩⟩
  have h₂ : Ico a d ∩ Ioc 0 T ⊆ Icc (max a 0) (min d T) := by
    intro x hx
    exact ⟨max_le hx.1.1 hx.2.1.le, le_min hx.1.2.le hx.2.2⟩
  have m₁ := measure_mono (μ := volume) h₁
  have m₂ := measure_mono (μ := volume) h₂
  rw [Real.volume_Ioo] at m₁
  rw [Real.volume_Icc] at m₂
  have hm : volume (Ico a d ∩ Ioc 0 T) = ENNReal.ofReal (min d T - max a 0) :=
    le_antisymm m₂ m₁
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, hm, ENNReal.toReal_ofReal']
  exact max_comm _ _

private lemma area_all {M : ℕ} (s : Finset (Fin M)) (a d : Fin M → ℝ)
    (T : ℝ) (hT : 0 ≤ T) :
    area s a d T = ∑ i ∈ s, timeInWindow a d T i := by
  unfold area numIn
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => indicator_area (a i) (d i) T hT)
  · intro i _
    apply MeasureTheory.Integrable.intervalIntegrable
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ico]
    exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ico])

private lemma area_counted {M : ℕ} (s : Finset (Fin M)) (a d : Fin M → ℝ)
    (T : ℝ) (hT : 0 < T) :
    area s a d T = ∑ i ∈ countedItems s a d T, timeInWindow a d T i := by
  classical
  rw [area_all s a d T hT.le, countedItems, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · unfold timeInWindow
    apply max_eq_left
    by_cases ha : a i < 0
    · have hd : d i ≤ 0 := le_of_not_gt (fun hd => hi (Or.inl ⟨ha, hd⟩))
      have hmin := min_le_left (d i) T
      have hmax := le_max_right (a i) 0
      linarith
    · have ha₀ : 0 ≤ a i := le_of_not_gt ha
      have ht : T < a i := lt_of_not_ge (fun ht => hi (Or.inr ⟨ha₀, ht⟩))
      have hmin := min_le_right (d i) T
      have hmax := le_max_left (a i) 0
      linarith

private lemma finite_window_identity {M : ℕ} (s : Finset (Fin M))
    (a d : Fin M → ℝ) (T : ℝ) (hT : 0 < T) :
    Lw s a d T = lamw s a d T * Ww s a d T := by
  have harea := area_counted s a d T hT
  unfold Lw lamw Ww
  rw [harea]
  by_cases hc : cumCount s a d T = 0
  · have hempty : countedItems s a d T = ∅ := by
      apply Finset.card_eq_zero.mp
      change ((countedItems s a d T).card : ℝ) = 0 at hc
      exact_mod_cast hc
    simp [hc, hempty]
  · field_simp

theorem solution {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) (hT : 0 < T)
    (had : ∀ i, a i ≤ d i) :
    area Finset.univ a d T =
        ∑ i ∈ countedItems Finset.univ a d T, timeInWindow a d T i ∧
      Ww Finset.univ a d T = area Finset.univ a d T / cumCount Finset.univ a d T := by
  have harea := area_counted Finset.univ a d T hT
  exact ⟨harea, by unfold Ww; rw [harea]⟩

#print axioms solution
