-- Prove2me | solution 1 for LiquidPoA.Kelly.kelly_zero_not_eq
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:44:04.171803+00:00
-- url     : https://prove2.me/submissions/aadccccd-3fbc-4069-98c6-c99880e6bd8a

import Definitions.Def_LiquidPoA_Kelly_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset LiquidPoA.Kelly

theorem solution {n : ℕ} (G : RAGame n)
    (hG : G.IsAdmissible) (i : Fin n)
    (hc : 0 < G.c i) (hv : G.v i 0 < G.v i 1) :
    ¬ IsEquilibrium (kelly n) G 0 := by
  obtain ⟨b, hb0, hbpos, hbbudget⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
  have hb : 0 < b := ENNReal.ofReal_pos.1 hbpos
  let ε := min (b / 2) ((G.v i 1 - G.v i 0) / 2)
  have hε : 0 < ε := lt_min (by positivity) (by linarith)
  have hεb : ε ≤ b := (min_le_left _ _).trans (by linarith)
  have hεgap : ε < G.v i 1 - G.v i 0 := by
    have := min_le_right (b / 2) ((G.v i 1 - G.v i 0) / 2)
    dsimp only [ε]
    linarith
  intro heq
  have haff : Affordable (kelly n) G (Function.update (0 : Fin n → ℝ) i ε) i := by
    change ENNReal.ofReal ((Function.update (0 : Fin n → ℝ) i ε) i) ≤ G.c i
    simp only [Function.update_self]
    exact (ENNReal.ofReal_le_ofReal hεb).trans hbbudget.le
  have hdev := (heq.2 i).2 ε hε.le haff
  have hsum : ∑ j : Fin n, Function.update (0 : Fin n → ℝ) i ε j = ε := by
    calc
      _ = Function.update (0 : Fin n → ℝ) i ε i := by
        apply sum_eq_single i
        · intro j _ hji
          simp [Function.update_of_ne hji]
        · simp
      _ = ε := by simp
  have halloc : (kelly n).alloc (Function.update (0 : Fin n → ℝ) i ε) i = 1 := by
    simp only [kelly, hsum, Function.update_self, div_self hε.ne']
  change G.v i ((kelly n).alloc (Function.update (0 : Fin n → ℝ) i ε) i) -
      (Function.update (0 : Fin n → ℝ) i ε) i ≤ G.v i ((kelly n).alloc 0 i) - 0 at hdev
  rw [halloc, Function.update_self] at hdev
  have hzero : (kelly n).alloc 0 i = 0 := by simp [kelly]
  rw [hzero] at hdev
  linarith

#print axioms solution
