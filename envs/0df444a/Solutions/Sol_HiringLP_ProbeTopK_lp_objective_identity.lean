-- Prove2me | solution 1 for HiringLP.ProbeTopK.lp_objective_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:36:03.463991+00:00
-- url     : https://prove2.me/submissions/5bafcceb-0aec-45db-95ab-e32957d1bcd5

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

set_option autoImplicit false
open HiringLP.ProbeTopK

theorem solution {n J : ℕ} (I : Instance n J)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hfeas : LPFeasible I x y) :
    LPobj I x y = ∑ i, y i * vbar I x i * pbar x y i := by
  obtain ⟨h1, -, -, h0, hy⟩ := hfeas
  unfold LPobj
  refine Finset.sum_congr rfl fun i _ => ?_
  have hzero : y i = 0 ∨ ∑ j, x i j = 0 → ∀ j, x i j = 0 := by
    intro h j
    rcases h with h | h
    · have := h1 i j
      rw [h] at this
      linarith [h0 i j]
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h0 i j)).1 h j (Finset.mem_univ _)
  by_cases hyi : y i = 0
  · have := hzero (Or.inl hyi)
    simp [pbar, hyi, this]
  by_cases hX : ∑ j, x i j = 0
  · have := hzero (Or.inr hX)
    simp [this, vbar]
  · simp only [pbar, vbar, hyi, hX, if_false]
    field_simp

