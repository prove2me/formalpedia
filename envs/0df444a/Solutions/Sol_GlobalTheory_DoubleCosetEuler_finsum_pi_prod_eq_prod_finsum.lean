-- Prove2me | solution 1 for GlobalTheory.DoubleCosetEuler.finsum_pi_prod_eq_prod_finsum
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T13:18:13.247773+00:00
-- url     : https://prove2.me/submissions/fc0fc2db-2cba-4331-a8fc-8ebfad570af1

import Mathlib

open Finset Function

theorem solution (J : Type) [Fintype J] (α : J → Type) (f : ∀ j, α j → ℂ)
    (hf : ∀ j, (Function.support (f j)).Finite) :
    ∑ᶠ y : (∀ j, α j), ∏ j, f j (y j) = ∏ j, ∑ᶠ a, f j a := by
  classical
  let s : ∀ j, Finset (α j) := fun j => (hf j).toFinset
  have hs : ∀ j a, a ∈ s j ↔ f j a ≠ 0 := by
    intro j a
    simp [s, Set.Finite.mem_toFinset, Function.mem_support]
  -- RHS: each finsum is a sum over the finite support, then distribute the product.
  have hR : ∏ j, ∑ᶠ a, f j a = ∑ y ∈ Fintype.piFinset s, ∏ j, f j (y j) := by
    have h1 : ∏ j, ∑ᶠ a, f j a = ∏ j, ∑ a ∈ s j, f j a := by
      apply Finset.prod_congr rfl
      intro j _
      apply finsum_eq_sum_of_support_subset
      intro a ha
      simpa [s, Set.Finite.coe_toFinset] using ha
    rw [h1, Finset.prod_univ_sum]
  -- LHS: the product function has finite support inside the pi of the supports.
  have hL : ∑ᶠ y : (∀ j, α j), ∏ j, f j (y j) = ∑ y ∈ Fintype.piFinset s, ∏ j, f j (y j) := by
    apply finsum_eq_sum_of_support_subset
    intro y hy
    rw [Fintype.coe_piFinset, Set.mem_pi]
    intro j _
    have hy' : ∏ j, f j (y j) ≠ 0 := by simpa [Function.mem_support] using hy
    have hj : f j (y j) ≠ 0 := Finset.prod_ne_zero_iff.mp hy' j (Finset.mem_univ j)
    simpa [s, Set.Finite.coe_toFinset, Function.mem_support] using hj
  rw [hL, hR]