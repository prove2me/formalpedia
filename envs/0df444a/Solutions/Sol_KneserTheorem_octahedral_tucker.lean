-- Prove2me | solution 1 for KneserTheorem.octahedral_tucker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:04:41.933367+00:00
-- url     : https://prove2.me/submissions/cbde8248-db61-4a57-9c7b-a0836437fb7c

module
public import Mathlib
public import Definitions.Def_KneserLib_Kneser
public import Definitions.Def_KneserLovasz_Solution
public import Theorems.Thm_KneserColouring_octahedral_tucker


set_option autoImplicit true
@[expose] public section
public section
open KneserTheorem
namespace KneserTheorem
theorem _root_.solution {n m : ℕ} (lab : (Fin n → SignType) → ℤ)
    (hlab : ∀ x, x ≠ 0 → lab x ≠ 0 ∧ |lab x| ≤ m)
    (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x) (hm : m < n) :
    ∃ x y : Fin n → SignType, x ≠ 0 ∧ (∀ i, x i ≠ 0 → x i = y i) ∧ lab x = -lab y :=
  KneserColouring.octahedral_tucker lab hlab hanti hm
end KneserTheorem
