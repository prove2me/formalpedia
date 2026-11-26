-- Prove2me | solution 1 for Lautemann.card_le_mul_card_of_shift_cover
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:54.784166+00:00
-- url     : https://prove2.me/submissions/01de4f1b-7a54-4ff2-9ba5-1ccec5b05872

import Mathlib



theorem solution {G : Type*} [Group G] [Fintype G]
    (pass : G → Bool) (t : ℕ) (shifts : Fin t → G)
    (each : ∀ seed : G, ∃ j, pass (seed * shifts j) = true) :
    Fintype.card G ≤ t * Fintype.card {r : G // pass r = true} := by
  classical
  let f (x : Fin t × {r : G // pass r = true}) := x.2.val * (shifts x.1)⁻¹
  have onto : Function.Surjective f := by
    intro seed
    obtain ⟨j, accepted⟩ := each seed
    refine ⟨(j,⟨seed*shifts j,accepted⟩),?_⟩
    simp [f]
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_le_of_surjective f onto
