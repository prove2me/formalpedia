-- Prove2me | solution 1 for LeaseModular.JointChoice.pi_SI_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:02:47.203188+00:00
-- url     : https://prove2.me/submissions/5a9dfcce-1450-423f-a05a-23d441f30205

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

open LeaseModular.JointChoice

theorem solution (P : Params) (hP : Standing P) :
    IsOptSI P ((2 - 4 * P.c + P.δ₁ + P.δ₂) ^ 2 / (8 * (2 + 3 * (P.δ₁ + P.δ₂)))) ∧
      ∀ S ∈ feasSI,
        profitSI P S = (2 - 4 * P.c + P.δ₁ + P.δ₂) ^ 2 / (8 * (2 + 3 * (P.δ₁ + P.δ₂))) ↔
          S = (2 - 4 * P.c + P.δ₁ + P.δ₂) / (2 * (2 + 3 * (P.δ₁ + P.δ₂))) := by
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl⟩ := hP
  have hD : 0 < 2 + 3 * (P.δ₁ + P.δ₂) := by linarith
  set S0 := (2 - 4 * P.c + P.δ₁ + P.δ₂) / (2 * (2 + 3 * (P.δ₁ + P.δ₂))) with hS0
  have key : ∀ S, profitSI P S = (2 - 4 * P.c + P.δ₁ + P.δ₂) ^ 2 / (8 * (2 + 3 * (P.δ₁ + P.δ₂)))
      - (2 + 3 * (P.δ₁ + P.δ₂)) / 2 * (S - S0) ^ 2 := by
    intro S
    unfold profitSI pSI
    rw [hS0]
    have hDne := hD.ne'
    generalize hE : 2 + 3 * (P.δ₁ + P.δ₂) = E at *
    field_simp
    subst hE
    ring
  have hS0pos : 0 ≤ S0 := by
    rw [hS0]; apply div_nonneg <;> linarith
  refine ⟨⟨⟨S0, hS0pos, by rw [key]; simp⟩, ?_⟩, ?_⟩
  · rintro v ⟨S, _, rfl⟩
    rw [key]
    have := mul_nonneg (by linarith : (0:ℝ) ≤ (2 + 3 * (P.δ₁ + P.δ₂)) / 2) (sq_nonneg (S - S0))
    linarith
  · intro S _
    rw [key]
    constructor
    · intro h
      have h2 : (2 + 3 * (P.δ₁ + P.δ₂)) / 2 * (S - S0) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
        linarith
    · intro h; rw [h]; simp
