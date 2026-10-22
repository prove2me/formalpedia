-- Prove2me | solution 1 for MangasarianFJ.GenFJ.system_2_18_no_solution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:38:06.101229+00:00
-- url     : https://prove2.me/submissions/8623a8c0-9799-495d-ada4-305732a18656

import Mathlib
import Definitions.Def_MangasarianFJ_GenFJ_Setting

set_option autoImplicit false
open MangasarianFJ.GenFJ

theorem solution {n m k : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n)) (hsol : IsSolution θ g h xbar) :
    xbar ∈ region g xbar ∧
    ((∀ i ∈ activeSet g xbar, g i xbar = 0) ∧ ∀ j, h j xbar = 0) ∧
    ¬ ∃ x ∈ region g xbar,
      θ x - θ xbar < 0 ∧ (∀ i ∈ activeSet g xbar, g i x < 0) ∧ ∀ j, h j x = 0 := by
  obtain ⟨⟨hfeas_g, hfeas_h⟩, hmin⟩ := hsol
  refine ⟨?_, ⟨fun i hi => hi, hfeas_h⟩, ?_⟩
  · intro i hi
    have h1 : g i xbar ≤ 0 := hfeas_g i
    have h2 : g i xbar ≠ 0 := fun h0 => hi h0
    exact lt_of_le_of_ne h1 h2
  · rintro ⟨x, hxD, hθ, hact, hh⟩
    have hfe : x ∈ feasibleSet g h := by
      refine ⟨fun i => ?_, hh⟩
      by_cases hi : i ∈ activeSet g xbar
      · exact (hact i hi).le
      · exact (hxD i hi).le
    have := hmin x hfe
    linarith

