-- Prove2me | solution 1 for KneserColouring.pref_update_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:14.147818+00:00
-- url     : https://prove2.me/submissions/91bfbda2-32b1-4812-81f8-e7d06beb6a58

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Theorems.Thm_KneserColouring_pref_congr


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}
namespace KneserColouring
theorem _root_.solution {t : Fin n → SignType} {ρ : Equiv.Perm (Fin n)} {c0 : Fin n}
    {v : SignType} {i : ℕ} (hi : i ≤ (ρ c0).val) :
    pref (Function.update t c0 v, ρ) i = pref (t, ρ) i := by
  apply pref_congr (r := (Function.update t c0 v, ρ)) (r' := (t, ρ)) (fun _ => Iff.rfl)
  intro c hc
  have : c ≠ c0 := by
    rintro rfl
    simp only at hc
    omega
  simp [Function.update_of_ne this]
end KneserColouring
