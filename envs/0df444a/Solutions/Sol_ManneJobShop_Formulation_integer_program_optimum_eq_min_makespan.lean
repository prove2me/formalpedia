-- Prove2me | solution 1 for ManneJobShop.Formulation.integer_program_optimum_eq_min_makespan
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:16:57.321008+00:00
-- url     : https://prove2.me/submissions/503e5714-9615-4f14-a124-ecedd39d314b

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



theorem goal_core {n : ℕ} [NeZero n] (I : Instance n) (t₀ : ℤ) :
    IsLeast {t : ℤ | ∃ x y, IsIPFeasible I x y t} t₀ ↔
      IsLeast (makespan I '' {x | IsSchedule I x}) t₀ := by
  have mk_le : ∀ x : Fin n → ℤ, ∀ t, makespan I x ≤ t ↔ ∀ j, x j + I.a j ≤ t := by
    intro x t
    unfold makespan
    rw [Finset.sup'_le_iff]
    simp
  have hmem : ∀ t, t ∈ {t : ℤ | ∃ x y, IsIPFeasible I x y t} ↔
      ∃ x, IsSchedule I x ∧ makespan I x ≤ t := by
    intro t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hxy⟩
      obtain ⟨h1, h2⟩ := (ip_core I x t).1 hxy
      exact ⟨x, h1, (mk_le x t).2 h2⟩
    · rintro ⟨x, h1, h2⟩
      obtain ⟨y, hy⟩ := (ip_core I x t).2 ⟨h1, (mk_le x t).1 h2⟩
      exact ⟨x, y, hy⟩
  constructor
  · rintro ⟨h0, hl⟩
    obtain ⟨x, hx, hle⟩ := (hmem t₀).1 h0
    have hge : t₀ ≤ makespan I x := hl ((hmem _).2 ⟨x, hx, le_rfl⟩)
    refine ⟨⟨x, hx, le_antisymm hle hge⟩, ?_⟩
    rintro s ⟨x', hx', rfl⟩
    exact hl ((hmem _).2 ⟨x', hx', le_rfl⟩)
  · rintro ⟨⟨x, hx, rfl⟩, hl⟩
    refine ⟨(hmem _).2 ⟨x, hx, le_rfl⟩, ?_⟩
    intro t ht
    obtain ⟨x', hx', hle⟩ := (hmem t).1 ht
    exact (hl ⟨x', hx', rfl⟩).trans hle

end ManneJobShop.Formulation

open ManneJobShop.Formulation


theorem solution {n : ℕ} [NeZero n] (I : Instance n) (t₀ : ℤ) :
    IsLeast {t : ℤ | ∃ x y, IsIPFeasible I x y t} t₀ ↔
      IsLeast (makespan I '' {x | IsSchedule I x}) t₀ := by
  exact goal_core I t₀
