-- Prove2me | solution 1 for NetworkControl.Backpressure.lemma_elementary_backlog_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:20:18.397433+00:00
-- url     : https://prove2.me/submissions/eb77930d-aceb-44dc-9b94-4606181fd720

import Mathlib

namespace NetworkControl.Backpressure

theorem aux_ebi_sq_le (V U μ A : ℝ) (hV : 0 ≤ V) (hU : 0 ≤ U) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (h : V ≤ max (U - μ) 0 + A) :
    V ^ 2 ≤ U ^ 2 + μ ^ 2 + A ^ 2 - 2 * U * (μ - A) := by
  rcases le_total (U - μ) 0 with h1 | h1
  · rw [max_eq_right h1] at h
    nlinarith
  · rw [max_eq_left h1] at h
    nlinarith

end NetworkControl.Backpressure

open NetworkControl.Backpressure

theorem solution
    (V U μ A : ℝ) (hV : 0 ≤ V) (hU : 0 ≤ U) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (h : V ≤ max (U - μ) 0 + A) :
    V ^ 2 ≤ U ^ 2 + μ ^ 2 + A ^ 2 - 2 * U * (μ - A) :=
  aux_ebi_sq_le V U μ A hV hU hμ hA h
