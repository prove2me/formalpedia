-- Prove2me | solution 1 for HerdingForecast.Equilibrium.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:22:29.350226+00:00
-- url     : https://prove2.me/submissions/2cb66d28-5899-407f-8c8d-9b4b5a7eb4b2

import Mathlib
import Definitions.Def_HerdingForecast_Equilibrium_Model
import Theorems.Thm_HerdingForecast_Equilibrium_ec_11_12_best_response
import Theorems.Thm_HerdingForecast_Equilibrium_ec_14_closed_form_solves
import Theorems.Thm_HerdingForecast_Equilibrium_ec_5_1_uniqueness

open HerdingForecast.Equilibrium

theorem solution (P : Params) (hP : Standing P) :
    IsEquilibrium P (closedForm P) ∧
      (∀ s : Profile P.K, IsEquilibrium P s → ∀ (k : Fin P.K) (x y : ℝ), (s k x y).1 = muMS P x y) ∧
      (∀ s : Profile P.K, IsEquilibrium P s → PolyGrowth s → s = closedForm P) := by
  -- an equilibrium solves the first-order conditions
  have foc : ∀ s : Profile P.K, IsEquilibrium P s →
      ∀ (k : Fin P.K) (x y : ℝ), s k x y = (brMean P s k x y, brVar P s k x y) := by
    intro s hs k x y
    obtain ⟨hpos, hlt⟩ := ec_11_12_best_response P hP s hs.1 k x y
    by_contra hne
    have h1 := hlt (s k x y) ((hs.1 k).2.1 x y) hne
    have h2 := hs.2 k x y (brMean P s k x y, brVar P s k x y) hpos
    linarith
  refine ⟨⟨(ec_14_closed_form_solves P hP).1, ?_⟩, ?_, ?_⟩
  · intro k x y a ha
    obtain ⟨hadm, hfix⟩ := ec_14_closed_form_solves P hP
    obtain ⟨hpos, hlt⟩ := ec_11_12_best_response P hP (closedForm P) hadm k x y
    rw [hfix k x y]
    by_cases hne : a = (brMean P (closedForm P) k x y, brVar P (closedForm P) k x y)
    · rw [hne]
    · exact le_of_lt (hlt a ha hne)
  · intro s hs
    exact (ec_5_1_uniqueness P hP s hs.1 (foc s hs)).1
  · intro s hs hg
    exact (ec_5_1_uniqueness P hP s hs.1 (foc s hs)).2 hg
