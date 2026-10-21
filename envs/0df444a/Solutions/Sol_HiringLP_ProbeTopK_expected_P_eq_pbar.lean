-- Prove2me | solution 1 for HiringLP.ProbeTopK.expected_P_eq_pbar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:37:54.803361+00:00
-- url     : https://prove2.me/submissions/a61b329a-3666-4d06-aa00-ab4df8989620

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

set_option autoImplicit false
open HiringLP.ProbeTopK

theorem solution {n J : ℕ} (I : Instance n J)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hfeas : LPFeasible I x y) (i : Fin n) :
    ∑ j, I.q i j * coin I x y i j = pbar x y i := by
  obtain ⟨h1, -, -, h0, hy⟩ := hfeas
  by_cases hyi : y i = 0
  · have : ∀ j, x i j = 0 := fun j => by
      have := h1 i j
      rw [hyi] at this
      linarith [h0 i j]
    simp [pbar, coin, hyi]
  · simp only [pbar, hyi, if_false]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hq : I.q i j = 0
    · have := h1 i j
      rw [hq] at this
      have hx : x i j = 0 := by linarith [h0 i j, this, mul_zero (y i)]
      simp [coin, hq, hx]
    · have : y i * I.q i j ≠ 0 := mul_ne_zero hyi hq
      simp only [coin, this, if_false]
      field_simp

