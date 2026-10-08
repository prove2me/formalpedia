-- Prove2me | solution 1 for ManneJobShop.Formulation.ip_feasible_iff_schedule
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:16:06.864356+00:00
-- url     : https://prove2.me/submissions/c1a127e1-bfd5-414e-acee-bd35794b14da

import Mathlib
import Definitions.Def_ManneJobShop_Formulation_Model



namespace ManneJobShop.Formulation

theorem ip_core {n : ℕ} (I : Instance n) (x : Fin n → ℤ) (t : ℤ) :
    (∃ y : Fin n → Fin n → ℤ, IsIPFeasible I x y t) ↔
      (IsSchedule I x ∧ ∀ j, x j + I.a j ≤ t) := by
  constructor
  · rintro ⟨y, hb, hc, hp, hd, hdue, ht⟩
    refine ⟨⟨hb, ?_, hp, hd, hdue⟩, ht⟩
    intro p hpc
    obtain ⟨⟨h0, h1⟩, h3, h4⟩ := hc p hpc
    have : y p.1 p.2 = 0 ∨ y p.1 p.2 = 1 := by omega
    rcases this with h | h
    · rw [h] at h3; left; linarith
    · rw [h] at h4; right; linarith
  · rintro ⟨⟨hb, hc, hp, hd, hdue⟩, ht⟩
    refine ⟨fun j k => if x j - x k ≥ I.a k then 0 else 1, hb, ?_, hp, hd, hdue, ht⟩
    intro p hpc
    have h1 := hb p.1
    have h2 := hb p.2
    have hcp := hc p hpc
    by_cases h : x p.1 - x p.2 ≥ I.a p.2
    · simp only [h, if_true]
      refine ⟨⟨le_rfl, by norm_num⟩, by linarith, by linarith⟩
    · simp only [h, if_false]
      have : x p.2 - x p.1 ≥ I.a p.1 := by
        rcases hcp with h' | h'
        · exact absurd h' h
        · exact h'
      refine ⟨⟨by norm_num, le_rfl⟩, by linarith, by linarith⟩

end ManneJobShop.Formulation

open ManneJobShop.Formulation


theorem solution {n : ℕ} (I : Instance n) (x : Fin n → ℤ) (t : ℤ) :
    (∃ y : Fin n → Fin n → ℤ, IsIPFeasible I x y t) ↔
      (IsSchedule I x ∧ ∀ j, x j + I.a j ≤ t) := by
  exact ip_core I x t
