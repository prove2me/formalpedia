-- Prove2me | solution 1 for Gilbreath.extension_interval_criterion
-- status  : ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-09-26T00:15:10.759338+00:00
-- url     : https://prove2.me/submissions/1e74358f-1d3c-452d-80f2-ce3af7cf1df9

import Definitions.Def_gilbreath_finite_extension

set_option autoImplicit false
open Gilbreath

private theorem distance_le (x a L : ℕ) :
    Int.natAbs ((x : ℤ) - (a : ℤ)) ≤ L ↔ x ≤ a + L ∧ a ≤ x + L := by
  by_cases h : a ≤ x
  · have he : (x : ℤ) - (a : ℤ) = ((x - a : ℕ) : ℤ) := by omega
    rw [he, Int.natAbs_natCast]
    omega
  · have he : (x : ℤ) - (a : ℤ) = -((a - x : ℕ) : ℤ) := by omega
    rw [he, Int.natAbs_neg, Int.natAbs_natCast]
    omega

theorem solution (es : List ℕ) :
    (∀ x : ℕ, extensionFold es x ≤ 1 ↔ x ≤ es.sum + 1) ↔
      ExtensionComplete es := by
  induction es with
  | nil => simp [extensionFold, ExtensionComplete]
  | cons a es ih =>
      change (∀ x : ℕ, extensionFold es (Int.natAbs ((x : ℤ) - (a : ℤ))) ≤ 1 ↔
        x ≤ (a + es.sum) + 1) ↔ (a ≤ es.sum + 1 ∧ ExtensionComplete es)
      constructor
      · intro hall
        have htail : ∀ y : ℕ, extensionFold es y ≤ 1 ↔ y ≤ es.sum + 1 := by
          intro y
          simpa [Nat.add_assoc] using hall (a + y)
        have hz : extensionFold es a ≤ 1 := by
          simpa using (hall 0).mpr (by omega)
        exact ⟨(htail a).mp hz, ih.mp htail⟩
      · rintro ⟨ha, hc⟩
        have htail := ih.mpr hc
        intro x
        rw [htail, distance_le]
        omega

#print axioms solution
