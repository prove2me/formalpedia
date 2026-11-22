-- Prove2me | solution 1 for Ironclad.alphaPiMu_eq_alphaClosed
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:06:05.62552+00:00
-- url     : https://prove2.me/submissions/738d511f-56df-48c7-ad67-4155dee0d7a3

import Mathlib
import Definitions.Def_Ironclad_ClosedForms

set_option autoImplicit false

open Ironclad

theorem solution (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) (θ : ℝ) :
    alphaPiMu ph q Δ θ = alphaClosed ph q Δ θ := by
  have hy0 : 0 < qH ph q := mul_pos hq0 hph0
  have hy1 : qH ph q < 1 := by unfold qH; nlinarith
  have hx0 : 0 < qh ph q := mul_pos (by linarith) hph0
  have hrel : qh ph q + qH ph q = ph := by unfold qh qH; ring
  have ha0 : 0 < (1 - ph) ^ Δ := pow_pos (by linarith) Δ
  have ha1 : (1 - ph) ^ Δ < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hb0 : 0 < (1 - qH ph q) ^ Δ := pow_pos (by linarith) Δ
  have hb1 : (1 - qH ph q) ^ Δ < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have h2 : (1 - ph) ^ (2 * Δ) = ((1 - ph) ^ Δ) ^ 2 := by rw [mul_comm, pow_mul]
  have hmean : meanCycle ph q Δ = 1 / (qH ph q + qh ph q * (1 - qH ph q) ^ Δ) := by
    simp only [meanCycle, muSoj, Fin.sum_univ_three, piStat, Pmat, lmat, patProb, patMeanLen,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    generalize (1 - ph) ^ Δ = a at *
    generalize (1 - qH ph q) ^ Δ = b at *
    generalize qh ph q = x at *
    generalize qH ph q = y at *
    subst hrel
    have e1 : x + y ≠ 0 := by positivity
    have e2 : y ≠ 0 := hy0.ne'
    have e3 : 1 - a ≠ 0 := by linarith
    have e4 : 1 - b ≠ 0 := by linarith
    have e5 : x * a + y * b ≠ 0 := by positivity
    have e6 : y + x * b ≠ 0 := by positivity
    field_simp
    ring
  have hS : ∑ i, piStat ph q Δ i * Pmat ph q Δ i 0 =
      (1 - qH ph q) ^ Δ * (qh ph q * (1 - ph) ^ Δ + qH ph q) /
        (qH ph q + qh ph q * (1 - qH ph q) ^ Δ) := by
    simp only [Fin.sum_univ_three, piStat, Pmat, patProb,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    generalize (1 - ph) ^ Δ = a at *
    generalize (1 - qH ph q) ^ Δ = b at *
    generalize qh ph q = x at *
    generalize qH ph q = y at *
    subst hrel
    have e1 : x + y ≠ 0 := by positivity
    have e2 : y ≠ 0 := hy0.ne'
    have e6 : y + x * b ≠ 0 := by positivity
    field_simp
    ring
  simp only [alphaPiMu]
  rw [hmean, hS]
  simp only [alphaClosed, piStat, Pmat, patProb, h2,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  generalize (1 - ph) ^ Δ = a at *
  generalize (1 - qH ph q) ^ Δ = b at *
  generalize qh ph q = x at *
  generalize qH ph q = y at *
  subst hrel
  have e1 : x + y ≠ 0 := by positivity
  have e2 : y ≠ 0 := hy0.ne'
  have e5 : x * a + y * b ≠ 0 := by positivity
  have e6 : y + x * b ≠ 0 := by positivity
  have e7 : x * a + y ≠ 0 := by positivity
  have e8 : b ≠ 0 := hb0.ne'
  field_simp
  ring
