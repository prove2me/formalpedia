-- Prove2me | solution 1 for Gilbreath.criterion
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T19:22:53.799663+00:00
-- url     : https://prove2.me/submissions/1ea4bc48-0407-41a8-9358-fe1bbf60d62f

import Definitions.Def_gilbreath_triangle
import Theorems.Thm_Gilbreath_propagation

open Gilbreath

theorem solution
    (h : ∀ K : ℕ, ∃ k m : ℕ, 1 ≤ k ∧ k + m = K + 1 ∧ d k 0 = 1 ∧
      ∀ n, 1 ≤ n → n ≤ m → d k n = 0 ∨ d k n = 2) (K : ℕ) : d (K + 1) 0 = 1 := by
  obtain ⟨k, m, _hk, hkm, hd0, hd⟩ := h K
  have hp := propagation (d k) m hd0 hd m le_rfl
  rw [iterAbsDiff_d, hkm] at hp
  exact hp
