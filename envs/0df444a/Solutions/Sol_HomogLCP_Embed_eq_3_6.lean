-- Prove2me | solution 1 for HomogLCP.Embed.eq_3_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:22:30.548397+00:00
-- url     : https://prove2.me/submissions/e3fcdb70-a3f0-47fb-b583-6954999f5d48

import Mathlib

set_option autoImplicit false

open Matrix

theorem solution {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : (M + Mᵀ).PosSemidef) :
    ∀ z : Fin d → ℝ, z ⬝ᵥ (M *ᵥ z) = 0 ↔ (M + Mᵀ) *ᵥ z = 0 := by
  intro z
  have h := hM.dotProduct_mulVec_zero_iff z
  have hT : z ⬝ᵥ (Mᵀ *ᵥ z) = z ⬝ᵥ (M *ᵥ z) := by
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  have h2 : z ⬝ᵥ ((M + Mᵀ) *ᵥ z) = 2 * (z ⬝ᵥ (M *ᵥ z)) := by
    rw [add_mulVec, dotProduct_add, hT]; ring
  rw [star_trivial] at h
  rw [← h, h2]
  constructor
  · intro h0; rw [h0]; ring
  · intro h0; linarith
