-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_predictable_grid_past_event_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:34:43.525001+00:00
-- url     : https://prove2.me/submissions/c6912414-19e1-4302-ae9c-f606adb3b40c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_predictable_martingale_increment_zero
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (E : NNReal → Ω → Real) (hE : Martingale E F P)
    (W : ℕ → Ω → Real) (u : ℕ → NNReal) (hu : Monotone u)
    (hW : ∀ i, Measurable[F (u i)] (W i)) (C : Real)
    (hWBound : ∀ i w, ‖W i w‖ ≤ C)
    (n : ℕ) (s : NNReal) (hs : s ≤ u 0)
    (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ w in A, ∑ i ∈ Finset.range n,
       W i w * (E (u (i + 1)) w - E (u i) w) ∂P) = 0 := by
  have hTerm (i : ℕ) : Integrable
      (fun w => W i w * (E (u (i + 1)) w - E (u i) w)) P := by
    have hQ := (hE.integrable (u (i + 1))).sub (hE.integrable (u i))
    exact hQ.bdd_mul ((hW i).mono (F.le _) le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall (hWBound i))
  have hZero (i : ℕ) :
      (∫ w in A, W i w * (E (u (i + 1)) w - E (u i) w) ∂P) = 0 := by
    have hsi : s ≤ u i := hs.trans (hu (Nat.zero_le i))
    have hAi : MeasurableSet[F (u i)] A := (F.mono hsi) A hA
    have hWi : Measurable[F (u i)] (A.indicator (W i)) :=
      (hW i).indicator hAi
    have hBound : ∀ w, ‖A.indicator (W i) w‖ ≤ C := by
      intro w
      by_cases hw : w ∈ A
      · simpa [Set.indicator_of_mem hw] using hWBound i w
      · have hc : 0 ≤ C := (norm_nonneg (W i w)).trans (hWBound i w)
        simpa [Set.indicator, hw] using hc
    have hZ := Kyprianou.Ch04.kw47_predictable_martingale_increment_zero
      P F E hE (A.indicator (W i))
      (u i) (u (i + 1)) (hu (Nat.le_succ i)) hWi C hBound
    have hAmbient : MeasurableSet A := (F.le s) A hA
    have hPt : (fun w : Ω =>
        A.indicator (fun v => W i v *
          (E (u (i + 1)) v - E (u i) v)) w) =
        (fun w : Ω => A.indicator (W i) w *
          (E (u (i + 1)) w - E (u i) w)) := by
      funext w
      by_cases hw : w ∈ A <;> simp [Set.indicator, hw]
    rw [← integral_indicator hAmbient, hPt]
    exact hZ
  rw [integral_finsetSum (Finset.range n)
    (fun i _ => (hTerm i).integrableOn)]
  simp [hZero]
