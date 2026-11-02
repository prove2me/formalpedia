-- Prove2me | solution 1 for MemoryScreen.Menu.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:27:50.126718+00:00
-- url     : https://prove2.me/submissions/6ef4945b-b1cc-423d-8bd7-31e297a6a489

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model
import Theorems.Thm_MemoryScreen_Menu_binding_reduction
import Theorems.Thm_MemoryScreen_Menu_ic_low_high
import Theorems.Thm_MemoryScreen_Menu_reduced_maximizer
import Theorems.Thm_MemoryScreen_Menu_perfect_memory_derivative

open MeasureTheory
open MemoryScreen.Menu

theorem solution (P : Params) (hS : P.Standing) :
    (∃ M : Menu, IsOptimal P M ∧ M.pH = P.c ∧ M.pL = pStarL P) ∧
    (∀ bl bu : ℝ, bl < P.αL - pStarL P → P.αH - P.c < bu →
      (∀ b ∈ Set.Ioo bl bu, 0 < P.f b) →
      ∀ M : Menu, IsOptimal P M → M.pH = P.c ∧ M.pL = pStarL P) ∧
    (∀ pB lo hi : ℝ, PeakedAt (perfectObj P P.c) pB lo hi →
      pStarL P ∈ Set.Ioo lo hi →
      (pStarL P < pB ↔
        P.f (P.αL - pStarL P) <
          (F P (P.αH - pStarL P) - F P (P.αL - pStarL P)) /
            (P.αH - P.αL))) := by
  obtain ⟨hB1, hB2, -⟩ := binding_reduction P hS
  obtain ⟨hR1, hR2⟩ := reduced_maximizer P hS
  obtain ⟨hD1, hD2⟩ := perfect_memory_derivative P hS
  have hFeas : Feasible P (bindingMenu P P.c (pStarL P)) :=
    ic_low_high P hS P.c (pStarL P) (by
      unfold pStarL
      have h1 : 0 < P.θ / (1 - P.θ) := div_pos hS.2.1 (by linarith [hS.2.2.1])
      have h2 : 0 < P.αH - P.αL := by linarith [hS.1]
      nlinarith [mul_pos h1 h2])
  have hOpt : IsOptimal P (bindingMenu P P.c (pStarL P)) := by
    refine ⟨hFeas, fun M' hM' => ?_⟩
    rw [hB2]
    exact (hB1 M' hM').trans (hR1 _ _)
  refine ⟨⟨_, hOpt, rfl, rfl⟩, ?_, ?_⟩
  · intro bl bu hbl hbu hpos M hM
    apply hR2 bl bu hbl hbu hpos
    have h1 := hB1 M hM.1
    have h2 := hM.2 _ hFeas
    rw [hB2] at h2
    have h3 := hR1 M.pH M.pL
    linarith
  · intro pB lo hi hpk hmem
    obtain ⟨hlo, hhi, hmax, hinc, hdec⟩ := hpk
    rw [← hD2]
    constructor
    · intro hlt
      exact hinc _ ⟨hmem.1, hlt⟩
    · intro hpos
      rcases lt_trichotomy (pStarL P) pB with h | h | h
      · exact h
      · exfalso
        have hz : deriv (perfectObj P P.c) pB = 0 :=
          IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall hmax)
        rw [h] at hpos; linarith
      · exfalso
        have := hdec _ ⟨h, hmem.2⟩
        linarith

