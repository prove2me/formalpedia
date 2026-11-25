-- Prove2me | solution 1 for HiltonMilner.Cross.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:54:19.346087+00:00
-- url     : https://prove2.me/submissions/ac1ab387-7539-4f82-8fe3-87747a272fd9

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
namespace Cross
theorem _root_.solution {𝒜 ℬ 𝒜' ℬ' : Finset (Finset ℕ)} (h : Cross 𝒜 ℬ) (h𝒜 : 𝒜' ⊆ 𝒜)
    (hℬ : ℬ' ⊆ ℬ) : Cross 𝒜' ℬ' :=
  fun A hA B hB => h A (h𝒜 hA) B (hℬ hB)
end Cross
end HiltonMilner
