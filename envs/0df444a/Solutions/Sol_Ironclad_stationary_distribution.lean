-- Prove2me | solution 1 for Ironclad.stationary_distribution
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:08:24.274044+00:00
-- url     : https://prove2.me/submissions/0a913d41-4a4d-4721-aeda-2e68863467ab

import Mathlib
import Definitions.Def_Ironclad_ClosedForms

set_option autoImplicit false

open Ironclad

theorem solution (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) :
    (∀ i, 0 ≤ piStat ph q Δ i) ∧ ∑ i, piStat ph q Δ i = 1 ∧
    Matrix.vecMul (piStat ph q Δ) (Pmat ph q Δ) = piStat ph q Δ ∧
    ∀ ν : Fin 3 → ℝ, (∀ i, 0 ≤ ν i) → ∑ i, ν i = 1 → Matrix.vecMul ν (Pmat ph q Δ) = ν →
      ν = piStat ph q Δ := by
  have hy0 : 0 < qH ph q := mul_pos hq0 hph0
  have hy1 : qH ph q < 1 := by unfold qH; nlinarith
  have hx0 : 0 < qh ph q := mul_pos (by linarith) hph0
  have hrel : qh ph q + qH ph q = ph := by unfold qh qH; ring
  have ha0 : 0 < (1 - ph) ^ Δ := pow_pos (by linarith) Δ
  have ha1 : (1 - ph) ^ Δ < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hb0 : 0 < (1 - qH ph q) ^ Δ := pow_pos (by linarith) Δ
  have hb1 : (1 - qH ph q) ^ Δ < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  simp only [piStat, Pmat, patProb]
  generalize (1 - ph) ^ Δ = a at *
  generalize (1 - qH ph q) ^ Δ = b at *
  generalize qh ph q = x at *
  generalize qH ph q = y at *
  subst hrel
  have e1 : x + y ≠ 0 := by positivity
  have e2 : y ≠ 0 := hy0.ne'
  have e6 : y + x * b ≠ 0 := by positivity
  have ha' : 0 < 1 - a := by linarith
  have hb' : 0 < 1 - b := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp <;> positivity
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  · funext j
    fin_cases j <;>
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> field_simp <;> ring
  · intro ν hν hs hst
    have E1 := congrFun hst 1
    have E2 := congrFun hst 2
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at E1 E2 hs
    have hA1 : x * (1 - a) / (x + y) * (x + y) = x * (1 - a) := by field_simp
    have hA2 : y * (1 - b) / (x + y) * (x + y) = y * (1 - b) := by field_simp
    have hB : y * (1 - b) / y = 1 - b := by field_simp
    have G2 : ν 2 * (y + x * b) = y * (1 - b) := by
      linear_combination (-(x + y)) * E2 + (ν 0 + ν 1) * hA2 + ν 2 * (x + y) * hB +
        y * (1 - b) * hs
    have F1 : ν 1 * (x + y) = (ν 0 + ν 1) * (x * (1 - a)) := by
      linear_combination (-(x + y)) * E1 + (ν 0 + ν 1) * hA1
    have G1' : (x + y) * (ν 1 * (y + x * b) - x * b * (1 - a)) = 0 := by
      linear_combination (y + x * b) * F1 + x * (1 - a) * (y + x * b) * hs
        - x * (1 - a) * G2
    have G1 : ν 1 * (y + x * b) = x * b * (1 - a) := by
      have := (mul_eq_zero.mp G1').resolve_left e1
      linarith
    have G0 : ν 0 * (y + x * b) = y * b + x * b * a := by
      linear_combination (y + x * b) * hs - G1 - G2
    have h0 : ν 0 = 1 / (y + x * b) * (y * b + x * b * a) := by
      field_simp; linarith
    have h1 : ν 1 = 1 / (y + x * b) * (x * b * (1 - a)) := by
      field_simp; linarith
    have h2 : ν 2 = 1 / (y + x * b) * (y * (1 - b)) := by
      field_simp; linarith
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
