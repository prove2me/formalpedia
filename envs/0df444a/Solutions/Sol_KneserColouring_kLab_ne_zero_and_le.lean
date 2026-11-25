-- Prove2me | solution 1 for KneserColouring.kLab_ne_zero_and_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:58:27.729981+00:00
-- url     : https://prove2.me/submissions/5f74afd3-ac89-4568-9012-5519381de852

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
public import Theorems.Thm_KneserColouring_one_le_suppCard
public import Theorems.Thm_KneserColouring_abs_kLab_small
public import Theorems.Thm_KneserColouring_kLab_large_bound

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q) (hk : 0 < k)
    {x : Fin n → SignType} (hx : x ≠ 0) :
    kLab c x ≠ 0 ∧ |kLab c x| ≤ ((2 * k - 2 + q : ℕ) : ℤ) := by
  by_cases hs : suppCard x ≤ 2 * k - 2
  · have h1 := abs_kLab_small c hs
    have h2 := one_le_suppCard hx
    constructor
    · intro h0
      rw [h0, abs_zero] at h1
      omega
    · rw [h1]
      omega
  · have := kLab_large_bound c hk hs
    constructor
    · intro h0
      rw [h0, abs_zero] at this
      omega
    · exact this.2
end KneserColouring
