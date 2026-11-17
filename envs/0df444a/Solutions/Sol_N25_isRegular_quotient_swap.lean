-- Prove2me | solution 1 for N25.isRegular_quotient_swap
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:00.914289+00:00
-- url     : https://prove2.me/submissions/b83c6314-65ce-4f49-abbd-7cc8ab021874

import Mathlib
import Theorems.Thm_N25_isLeftRegular_quotient_swap

/-! Regularity in monic root extensions and two-element regular-sequence swaps. -/
noncomputable section

namespace N25

open Polynomial

/-- In a commutative ring, regularity of `D` and of `c` modulo `(D)`
implies regularity of `D` modulo `(c)`. -/
theorem _root_.solution
    {B : Type*} [CommRing B] {D c : B}
    (hD : IsRegular D)
    (hc : IsRegular
      (Ideal.Quotient.mk (Ideal.span ({D} : Set B)) c)) :
    IsRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) := by
  have hleft : IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) :=
    isLeftRegular_quotient_swap hD.left hc.left
  refine ⟨hleft, ?_⟩
  intro x y hxy
  apply hleft
  simpa [mul_comm] using hxy

end N25
