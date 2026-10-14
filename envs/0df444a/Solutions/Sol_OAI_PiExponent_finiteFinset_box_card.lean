-- Prove2me | solution 1 for OAI.PiExponent.finiteFinset_box_card
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T16:23:13.825981+00:00
-- url     : https://prove2.me/submissions/b4c90ae6-afed-4f35-8ee1-f2951c2a5e93

import Mathlib.Tactic

theorem solution {m : ℕ}
    (S : Finset (Fin m →₀ ℕ)) (N : ℕ)
    (hbox : ∀ a ∈ S, ∀ i, a i < N) :
    Fintype.card {a // a ∈ S} ≤ N ^ m := by
  classical
  let encode : {a // a ∈ S} → (Fin m → Fin N) := fun a i =>
    ⟨a.1 i, hbox a.1 a.2 i⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have hi := congrFun hab i
    exact congrArg Fin.val hi
  calc
    Fintype.card {a // a ∈ S} ≤ Fintype.card (Fin m → Fin N) :=
      Fintype.card_le_of_injective encode hencode
    _ = N ^ m := by simp
