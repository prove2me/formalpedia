-- Prove2me | solution 1 for NewtonCartan.conn_eq_of_unitTimelike_quad
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:59:13.776284+00:00
-- url     : https://prove2.me/submissions/16f8e7fc-0b21-4634-b767-77de96f0bc94

import Definitions.Def_NewtonCartan_defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ContDiff BigOperators
open Classical
open NewtonCartan

private def ut (p q r : ℝ) : Fin 4 → ℝ := fun i =>
  if i = 0 then 1 else if i = 1 then p else if i = 2 then q else r

private lemma ut_val (p q r : ℝ) :
    ut p q r 0 = 1 ∧ ut p q r 1 = p ∧ ut p q r 2 = q ∧ ut p q r 3 = r := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  change (if (3 : Fin 4) = 0 then 1 else if 3 = 1 then p else if 3 = 2 then q else r) = r
  simp

private lemma slice_eq_zero (C : Fin 4 → Fin 4 → ℝ) (hsym : ∀ b c, C b c = C c b)
    (hquad : ∀ p q r : ℝ, (∑ b : Fin 4, ∑ c : Fin 4, C b c * ut p q r b * ut p q r c) = 0) :
    ∀ b c, C b c = 0 := by
  have hexpand (p q r : ℝ) :
      C 0 0 + 2 * C 0 1 * p + 2 * C 0 2 * q + 2 * C 0 3 * r +
        C 1 1 * p ^ 2 + C 2 2 * q ^ 2 + C 3 3 * r ^ 2 +
        2 * C 1 2 * p * q + 2 * C 1 3 * p * r + 2 * C 2 3 * q * r = 0 := by
    have h := hquad p q r
    have ⟨h0, h1, h2, h3⟩ := ut_val p q r
    have hs :
        (∑ b : Fin 4, ∑ c : Fin 4, C b c * ut p q r b * ut p q r c) =
          (C 0 0 * 1 * 1 + C 0 1 * 1 * p + C 0 2 * 1 * q + C 0 3 * 1 * r) +
          (C 1 0 * p * 1 + C 1 1 * p * p + C 1 2 * p * q + C 1 3 * p * r) +
          (C 2 0 * q * 1 + C 2 1 * q * p + C 2 2 * q * q + C 2 3 * q * r) +
          (C 3 0 * r * 1 + C 3 1 * r * p + C 3 2 * r * q + C 3 3 * r * r) := by
      simp only [Fin.sum_univ_four, h0, h1, h2, h3]
    rw [hs] at h
    simp only [hsym 1 0, hsym 2 0, hsym 3 0, hsym 2 1, hsym 3 1, hsym 3 2] at h
    ring_nf at h ⊢
    linarith
  have h00 : C 0 0 = 0 := by simpa using hexpand 0 0 0
  have line1 (t : ℝ) : 2 * C 0 1 * t + C 1 1 * t ^ 2 = 0 := by
    have := hexpand t 0 0; simp [h00] at this; linarith
  have h01 : C 0 1 = 0 := by
    have h1 := line1 1; have hm := line1 (-1); simp at h1 hm; linarith
  have h11 : C 1 1 = 0 := by have h1 := line1 1; simp [h01] at h1; linarith
  have line2 (t : ℝ) : 2 * C 0 2 * t + C 2 2 * t ^ 2 = 0 := by
    have := hexpand 0 t 0; simp [h00] at this; linarith
  have h02 : C 0 2 = 0 := by
    have h1 := line2 1; have hm := line2 (-1); simp at h1 hm; linarith
  have h22 : C 2 2 = 0 := by have h1 := line2 1; simp [h02] at h1; linarith
  have line3 (t : ℝ) : 2 * C 0 3 * t + C 3 3 * t ^ 2 = 0 := by
    have := hexpand 0 0 t; simp [h00] at this; linarith
  have h03 : C 0 3 = 0 := by
    have h1 := line3 1; have hm := line3 (-1); simp at h1 hm; linarith
  have h33 : C 3 3 = 0 := by have h1 := line3 1; simp [h03] at h1; linarith
  have h12 : C 1 2 = 0 := by
    have := hexpand 1 1 0
    simp [h00, h01, h02, h03, h11, h22, h33] at this; linarith
  have h13 : C 1 3 = 0 := by
    have := hexpand 1 0 1
    simp [h00, h01, h02, h03, h11, h22, h33, h12] at this; linarith
  have h23 : C 2 3 = 0 := by
    have := hexpand 0 1 1
    simp [h00, h01, h02, h03, h11, h22, h33, h12, h13] at this; linarith
  intro b c
  have h10 : C 1 0 = 0 := (hsym 1 0).trans h01
  have h20 : C 2 0 = 0 := (hsym 2 0).trans h02
  have h30 : C 3 0 = 0 := (hsym 3 0).trans h03
  have h21 : C 2 1 = 0 := (hsym 2 1).trans h12
  have h31 : C 3 1 = 0 := (hsym 3 1).trans h13
  have h32 : C 3 2 = 0 := (hsym 3 2).trans h23
  fin_cases b <;> fin_cases c <;>
    simp [h00, h01, h02, h03, h11, h12, h13, h22, h23, h33, h10, h20, h30, h21, h31, h32]

theorem solution (C : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym : ∀ a b c, C a b c = C a c b)
    (hquad : ∀ a (ξ : Fin 4 → ℝ), ξ 0 = 1 →
      (∑ b : Fin 4, ∑ c : Fin 4, C a b c * ξ b * ξ c) = 0) :
    ∀ a b c, C a b c = 0 := by
  intro a
  exact slice_eq_zero (C a) (fun b c => hsym a b c)
    (fun p q r => hquad a (ut p q r) rfl)
