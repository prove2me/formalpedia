-- Prove2me | solution 1 for OAI.KervaireRibbon.suppress_involutive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:57:12.476463+00:00
-- url     : https://prove2.me/submissions/56fba31f-0e56-45f6-982d-4dd089e55440

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]
omit [Fintype D] in
theorem solution (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    ∀ d, suppress θ x y (suppress θ x y d) = d := by
  intro d
  set a := θ x with ha
  let θ' : D → D := fun d => swap y a (θ (swap y a d))
  have hinv : ∀ d, θ' (θ' d) = d := by
    intro d; simp only [θ', swap_apply_self, hθ]
  have hya : y ≠ a := fun h => hxy' h.symm
  have hxa : x ≠ a := fun h => hx h.symm
  have h1 : θ' x = y := by
    simp only [θ']
    rw [swap_apply_of_ne_of_ne hxy hxa, ← ha, swap_apply_right]
  have h2 : θ' y = x := by
    simp only [θ']
    rw [swap_apply_left, ha, hθ, swap_apply_of_ne_of_ne hxy hxa]
  have hs : ∀ d, suppress θ x y d = swap x y (θ' d) := by
    intro d; simp only [suppress, Perm.mul_apply, θ']; rfl
  rw [hs, hs]
  by_cases hu1 : θ' d = x
  · rw [hu1, swap_apply_left, h2, swap_apply_left]
    have := congrArg θ' hu1; rw [hinv, h1] at this; exact this.symm
  by_cases hu2 : θ' d = y
  · rw [hu2, swap_apply_right, h1, swap_apply_right]
    have := congrArg θ' hu2; rw [hinv, h2] at this; exact this.symm
  rw [swap_apply_of_ne_of_ne hu1 hu2, hinv]
  have hdx : d ≠ x := fun h => hu2 (by rw [h, h1])
  have hdy : d ≠ y := fun h => hu1 (by rw [h, h2])
  exact swap_apply_of_ne_of_ne hdx hdy
