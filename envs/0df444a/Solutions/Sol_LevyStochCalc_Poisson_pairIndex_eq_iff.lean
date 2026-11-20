-- Prove2me | solution 1 for LevyStochCalc.Poisson.pairIndex_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T13:51:31.02838+00:00
-- url     : https://prove2.me/submissions/26361b6f-43df-4385-9aed-2228c17de95f

import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F000

open LevyStochCalc.Poisson in
theorem solution {p : ℕ} (k l k' l' : Fin p) :
    pairIndex k l = pairIndex k' l' ↔ (k = k' ∧ l = l') ∨ (k = l' ∧ l = k') := by
  constructor
  · intro h
    have h1 := congrFun h k
    have h2 := congrFun h l
    have h3 := congrFun h k'
    have h4 := congrFun h l'
    simp only [pairIndex] at h1 h2 h3 h4
    by_cases a : k = k' <;> by_cases b : l = l' <;> by_cases c : k = l' <;>
      by_cases d : l = k' <;> by_cases e : k = l <;> by_cases f : k' = l' <;>
      simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · funext j; simp only [pairIndex]; omega
