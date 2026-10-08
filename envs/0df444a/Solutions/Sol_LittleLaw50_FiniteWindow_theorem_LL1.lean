-- Prove2me | solution 1 for LittleLaw50.FiniteWindow.theorem_LL1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:30:41.830329+00:00
-- url     : https://prove2.me/submissions/be1b4c35-87c5-4207-aed9-46856c8c2107

import Mathlib
import Definitions.Def_LittleLaw50_FiniteWindow_EmptyWindow
import Theorems.Thm_KellyStochasticNetworks_littles_law_cycle_identity

open LittleLaw50.FiniteWindow

theorem solution {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) (hT : 0 < T)
    (hempty : ∀ i, 0 ≤ a i ∧ a i ≤ d i ∧ d i ≤ T) :
    L_LL1 a d T = lam_LL1 a T * W_LL1 a d T := by
  classical
  have hs : arrivalsIn a T = Finset.univ := by
    ext i
    simp [arrivalsIn, (hempty i).1, (hempty i).2.1.trans (hempty i).2.2]
  have hA : areaLL1 a d T = ∑ i, (d i - a i) :=
    KellyStochasticNetworks.littles_law_cycle_identity T a d
      (fun i => (hempty i).1) (fun i => (hempty i).2.1) (fun i => (hempty i).2.2)
  unfold L_LL1 lam_LL1 W_LL1
  rw [hA]
  simp only [numArrivals, hs, Finset.card_univ, Fintype.card_fin]
  by_cases hM : (M : ℝ) = 0
  · have hMnat : M = 0 := Nat.cast_eq_zero.mp hM
    subst M
    simp
  · field_simp [hM] <;> ring

#print axioms solution
