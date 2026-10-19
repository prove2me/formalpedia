-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.fiber_occupancy_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:44:18.639616+00:00
-- url     : https://prove2.me/submissions/0b2d276e-2988-43e7-9213-c6fa6d91c78d

import Mathlib
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators
theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (P : κ → Prop) [DecidablePred P] :
    (∑ a ∈ ((Finset.univ : Finset κ).filter P),
      (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ)) =
      (((Finset.univ : Finset ι).filter (fun i => P (group i))).card : ℝ) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := group) (t := (Finset.univ : Finset κ).filter P)
    (by intro i hi; simp at hi ⊢; exact hi)]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact ⟨h ▸ ha, h⟩
  · intro h; exact h.2
