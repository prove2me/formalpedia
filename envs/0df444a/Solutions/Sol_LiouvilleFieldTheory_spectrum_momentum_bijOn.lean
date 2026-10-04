-- Prove2me | solution 1 for LiouvilleFieldTheory.spectrum_momentum_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:46:21.124963+00:00
-- url     : https://prove2.me/submissions/830f5c48-cd14-44cc-86c8-4e4b3f572eaa

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics

open Complex

namespace LiouvilleFieldTheory

lemma cd_eq_2e3d83ec (b : ℂ) (P : ℝ) :
    conformalDimension b (backgroundCharge b / 2 + I * P) =
      (centralCharge b - 1) / 24 + ((P ^ 2 : ℝ) : ℂ) := by
  unfold conformalDimension centralCharge
  push_cast
  ring_nf
  rw [I_sq]
  ring

end LiouvilleFieldTheory

open Complex LiouvilleFieldTheory in
theorem solution (b : ℂ) :
    Set.BijOn (fun P : ℝ => conformalDimension b (backgroundCharge b / 2 + I * P))
      (Set.Ici 0)
      {Δ : ℂ | ∃ t : ℝ, 0 ≤ t ∧ Δ = (centralCharge b - 1) / 24 + t} := by
  refine ⟨?_, ?_, ?_⟩
  · intro P _
    exact ⟨P ^ 2, sq_nonneg P, cd_eq_2e3d83ec b P⟩
  · intro P hP P' hP' h
    simp only [cd_eq_2e3d83ec] at h
    have h2 : P ^ 2 = P' ^ 2 := by exact_mod_cast add_left_cancel h
    exact (sq_eq_sq₀ hP hP').1 h2
  · rintro Δ ⟨t, ht, rfl⟩
    refine ⟨Real.sqrt t, Real.sqrt_nonneg t, ?_⟩
    simp only [cd_eq_2e3d83ec, Real.sq_sqrt ht]
