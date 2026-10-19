-- Prove2me | solution 1 for GreenTao.coordinate_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:17:52.138966+00:00
-- url     : https://prove2.me/submissions/5e6f4853-0745-4b1d-90fe-8f8cf086bd44

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib

open scoped BigOperators
open GreenTao

private lemma avg_mul_cs {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun x => c * f x) = c * avg f := by
  simp only [avg, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private lemma avg_mul_avg_cs {α β : Type} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) : avg f * avg g = avg (fun x => avg fun y => f x * g y) := by
  simp only [avg, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private lemma avg_cs_weighted {α : Type} [Fintype α] (G H w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hG : ∀ a, |G a| ≤ w a) :
    (avg fun a => G a * H a) ^ 2 ≤ avg w * avg (fun a => w a * H a ^ 2) := by
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := (Finset.univ : Finset α))
    (r := fun a => G a * H a) (f := w) (g := fun a => w a * H a ^ 2)
    (fun a _ => hw a) (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
    (fun a _ => by
      have hsq : (G a) ^ 2 ≤ (w a) ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (hw a)).2 (hG a)
      nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (H a))])
  have hscale := mul_le_mul_of_nonneg_left hs (sq_nonneg ((Fintype.card α : ℝ)⁻¹))
  simpa only [avg, mul_pow, pow_two, mul_assoc, mul_left_comm, mul_comm] using hscale

theorem solution {α β : Type} [Fintype α] [Fintype β]
    (G w : α → ℝ) (H : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hG : ∀ a, |G a| ≤ w a) :
    (avg fun a => G a * avg (H a)) ^ 2 ≤
      avg w * avg (fun a => avg fun b => avg fun c => w a * H a b * H a c) := by
  have h := avg_cs_weighted G (fun a => avg (H a)) w hw hG
  have heq (a) : w a * avg (H a) ^ 2 =
      avg (fun b => avg fun c => w a * H a b * H a c) := by
    rw [pow_two, avg_mul_avg_cs]
    simp_rw [mul_assoc, avg_mul_cs]
  simpa only [heq] using h
