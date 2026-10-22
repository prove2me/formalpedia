-- Prove2me | solution 1 for LiquidPoA.Kelly.kelly_not_eq_one_positive
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:42:59.018798+00:00
-- url     : https://prove2.me/submissions/0ae364e6-710f-4198-b42c-940ed79553a9

import Definitions.Def_LiquidPoA_Kelly_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset LiquidPoA.Kelly

namespace D22KellySole

theorem total_eq_single {n : ℕ} (s : Fin n → ℝ) (i : Fin n)
    (hothers : ∀ j, j ≠ i → s j = 0) : ∑ j, s j = s i := by
  apply sum_eq_single i
  · intro j _ hji
    exact hothers j hji
  · simp

theorem update_total {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (b : ℝ)
    (hothers : ∀ j, j ≠ i → s j = 0) : ∑ j, Function.update s i b j = b := by
  rw [total_eq_single _ i]
  · simp
  · intro j hji
    simpa [Function.update_of_ne hji] using hothers j hji

end D22KellySole

theorem solution {n : ℕ} (G : RAGame n)
    (hG : G.IsAdmissible) (s : Fin n → ℝ) (hs : IsSignal s)
    (i : Fin n) (hi : 0 < s i)
    (hothers : ∀ j, j ≠ i → s j = 0) :
    ¬ IsEquilibrium (kelly n) G s := by
  intro heq
  have hbudget : ENNReal.ofReal (s i) ≤ G.c i := (heq.2 i).1
  have hhalf : 0 < s i / 2 := by positivity
  have haff : Affordable (kelly n) G (Function.update s i (s i / 2)) i := by
    change ENNReal.ofReal ((Function.update s i (s i / 2)) i) ≤ G.c i
    simp only [Function.update_self]
    exact (ENNReal.ofReal_le_ofReal (show s i / 2 ≤ s i by linarith)).trans hbudget
  have hdev := (heq.2 i).2 (s i / 2) hhalf.le haff
  have hsum := D22KellySole.total_eq_single s i hothers
  have hsumhalf := D22KellySole.update_total s i (s i / 2) hothers
  have hall : (kelly n).alloc s i = 1 := by
    simp only [kelly, hsum, div_self hi.ne']
  have hhalf_alloc : (kelly n).alloc (Function.update s i (s i / 2)) i = 1 := by
    simp only [kelly, hsumhalf, Function.update_self, div_self hhalf.ne']
  change G.v i ((kelly n).alloc (Function.update s i (s i / 2)) i) -
      (Function.update s i (s i / 2)) i ≤ G.v i ((kelly n).alloc s i) - s i at hdev
  rw [hhalf_alloc, hall, Function.update_self] at hdev
  linarith

#print axioms solution
