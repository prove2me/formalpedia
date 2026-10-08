-- Prove2me | solution 1 for LittleLaw50.FiniteWindow.theorem_LL2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:33:59.328827+00:00
-- url     : https://prove2.me/submissions/dd59e1a5-a0e5-42a8-887a-e027ebc29526

import Mathlib
import Definitions.Def_LittleLaw50_FiniteWindow_Window
import Theorems.Thm_LittleLaw50_FiniteWindow_area_eq_sum_timeInWindow

open LittleLaw50.FiniteWindow

theorem solution {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) (hT : 0 < T)
    (had : ∀ i, a i ≤ d i) :
    Lw Finset.univ a d T = lamw Finset.univ a d T * Ww Finset.univ a d T := by
  have harea := (area_eq_sum_timeInWindow a d T hT had).1
  unfold Lw lamw Ww
  rw [harea]
  by_cases hc : cumCount Finset.univ a d T = 0
  · have hempty : countedItems Finset.univ a d T = ∅ := by
      apply Finset.card_eq_zero.mp
      change ((countedItems Finset.univ a d T).card : ℝ) = 0 at hc
      exact_mod_cast hc
    simp [hc, hempty]
  · field_simp

#print axioms solution
