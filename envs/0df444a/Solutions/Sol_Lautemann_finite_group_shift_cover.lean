-- Prove2me | solution 1 for Lautemann.finite_group_shift_cover
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:21:48.958962+00:00
-- url     : https://prove2.me/submissions/2abf2271-c224-4059-aed4-09f8c8654101

import Mathlib

theorem solution {G : Type*} [Group G] [Fintype G]
    (pass : G → Bool) (t : ℕ)
    (few : Fintype.card G * Fintype.card {x : G // pass x = false} ^ t <
      Fintype.card G ^ t) :
    ∃ shifts : Fin t → G, ∀ seed : G, ∃ j, pass (seed * shifts j) = true := by
  classical
  let Bad := {x : G // pass x = false}
  let recover (p : G × (Fin t → Bad)) (j : Fin t) : G := p.1⁻¹ * (p.2 j).val
  by_contra! misses
  have onto : Function.Surjective recover := by
    intro shifts
    obtain ⟨seed, rejected⟩ := misses shifts
    let bad (j : Fin t) : Bad :=
      ⟨seed * shifts j, Bool.eq_false_iff.mpr (rejected j)⟩
    refine ⟨(seed, bad), ?_⟩
    funext j
    simp [recover, bad]
  have bound := Fintype.card_le_of_surjective recover onto
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at bound
  exact (Nat.not_le_of_lt few) bound
