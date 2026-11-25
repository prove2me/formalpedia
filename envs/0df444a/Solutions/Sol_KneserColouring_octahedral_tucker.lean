-- Prove2me | solution 1 for KneserColouring.octahedral_tucker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:02:00.147162+00:00
-- url     : https://prove2.me/submissions/08eab60b-df8f-4cb7-b171-b5b4ba8f9cf9

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerMain
public import Definitions.Def_KneserLib_KneserLabel
public import Definitions.Def_KneserLib_Kneser
public import Theorems.Thm_KneserColouring_tucker_core


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
namespace KneserColouring
theorem _root_.solution {n m : ℕ} (lab : (Fin n → SignType) → ℤ)
    (hlab : ∀ x, x ≠ 0 → lab x ≠ 0 ∧ |lab x| ≤ m)
    (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x) (hm : m < n) :
    ∃ x y : Fin n → SignType, x ≠ 0 ∧ (∀ i, x i ≠ 0 → x i = y i) ∧ lab x = -lab y := by
  by_contra h
  have hNC : NoCompLab lab := fun x y hx hxy heq => h ⟨x, y, hx, hxy, heq⟩
  have := tucker_core lab (fun x hx => (hlab x hx).2) hanti hNC (by omega)
  omega
end KneserColouring
