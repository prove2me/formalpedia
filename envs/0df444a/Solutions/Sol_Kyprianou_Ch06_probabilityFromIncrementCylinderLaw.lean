-- Prove2me | solution 1 for Kyprianou.Ch06.probabilityFromIncrementCylinderLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:07:17.290193+00:00
-- url     : https://prove2.me/submissions/2ecfbf20-8027-47fd-b151-00f32a6f41c2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory
open scoped NNReal

/-- The zero-dimensional cylinder identity in the Chapter 6 Lévy-process
independence axiom forces unit total mass. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hindep : ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
      StrictMono times →
      ∀ A : Fin n → Set Real, (∀ i, MeasurableSet (A i)) →
        P {ω | ∀ i : Fin n,
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i} =
        ∏ i : Fin n,
          P {ω |
            X (times i.succ) ω - X (times i.castSucc) ω ∈ A i}) :
    P (Set.univ : Set Ω) = 1 := by
  have hstrict : StrictMono (fun _ : Fin 1 => (0 : NNReal)) := by
    intro a b hab
    have ha : a = 0 := Subsingleton.elim a 0
    have hb : b = 0 := Subsingleton.elim b 0
    subst a
    subst b
    exact False.elim (lt_irrefl _ hab)
  have h := hindep 0 (fun _ : Fin 1 => (0 : NNReal)) hstrict
    (fun i : Fin 0 => Fin.elim0 i) (by intro i; exact Fin.elim0 i)
  simpa using h
