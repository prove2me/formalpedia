-- Prove2me | solution 1 for HiltonMilner.shift_mem_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:01:24.141225+00:00
-- url     : https://prove2.me/submissions/aae0b760-f0ec-46c6-8659-7e71379b9962

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Theorems.Thm_HiltonMilner_shiftSet_mem_sh

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {y z : ℕ} {𝒜 : Finset (Finset ℕ)} (hfix : sh y z 𝒜 = 𝒜) {A : Finset ℕ}
    (hA : A ∈ 𝒜) (hyA : y ∉ A) (hzA : z ∈ A) : insert y (A.erase z) ∈ 𝒜 := by
  have := shiftSet_mem_sh (y := y) (z := z) hA
  rw [hfix] at this
  unfold shiftSet at this
  rwa [if_pos ⟨hyA, hzA⟩] at this
end HiltonMilner
