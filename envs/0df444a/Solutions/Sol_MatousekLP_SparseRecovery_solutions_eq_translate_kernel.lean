-- Prove2me | solution 1 for MatousekLP.SparseRecovery.solutions_eq_translate_kernel
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:47:24.559765+00:00
-- url     : https://prove2.me/submissions/f88a4484-f7d4-4173-930e-0ece31eaf6ed

import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit
import Mathlib

open Matrix MatousekLP.SparseRecovery

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (z : Fin n → ℝ) (hz : A *ᵥ z = b) :
    {x : Fin n → ℝ | A *ᵥ x = b} = translate (kernel A) z := by
  ext x
  change A *ᵥ x = b ↔ ∃ l, A *ᵥ l = 0 ∧ x = l + z
  constructor
  · intro hx
    refine ⟨x - z, ?_, by abel⟩
    rw [mulVec_sub, hx, hz, sub_self]
  · rintro ⟨l, hl, rfl⟩
    rw [mulVec_add, hl, hz, zero_add]
