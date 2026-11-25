-- Prove2me | solution 1 for KneserColouring.exists_maxCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:27.964316+00:00
-- url     : https://prove2.me/submissions/87c0fad7-35c8-4bae-9cbf-8d011fe6b8c1

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (c : {s : Finset (Fin n) // s.card = k} → Fin q) {B : Finset (Fin n)}
    (h : 1 ≤ maxCol c B) :
    ∃ A, ∃ hA : A.card = k, A ⊆ B ∧ (c ⟨A, hA⟩).val + 1 = maxCol c B := by
  have hne : (B.powersetCard k).Nonempty := by
    by_contra h'
    rw [not_nonempty_iff_eq_empty] at h'
    simp [maxCol, h'] at h
  obtain ⟨A, hA, heq⟩ := exists_mem_eq_sup _ hne (setCol c)
  rw [mem_powersetCard] at hA
  refine ⟨A, hA.2, hA.1, ?_⟩
  rw [maxCol, heq]
  simp [setCol, hA.2]
end KneserColouring
