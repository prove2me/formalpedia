-- Prove2me | solution 1 for KneserColouring.kLab_large_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:57:36.566657+00:00
-- url     : https://prove2.me/submissions/f8ae1868-091f-4e41-8dc4-e7f6908976e3

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
public import Theorems.Thm_KneserColouring_maxCol_le
public import Theorems.Thm_KneserColouring_one_le_maxCol_of_large

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q) (hk : 0 < k)
    {x : Fin n → SignType} (hx : ¬ suppCard x ≤ 2 * k - 2) :
    2 * k - 1 ≤ |kLab c x| ∧ |kLab c x| ≤ ((2 * k - 2 + q : ℕ) : ℤ) := by
  have hmax := one_le_maxCol_of_large c hk hx
  have hp := maxCol_le c (posPart x)
  have hn := maxCol_le c (negPart x)
  unfold kLab
  rw [if_neg hx]
  split_ifs with h
  · rw [abs_of_nonneg (by positivity)]
    constructor <;> omega
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    constructor <;> omega
end KneserColouring
