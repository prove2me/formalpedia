-- Prove2me | solution 1 for HiltonMilner.shiftSet_mem_sh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:54:30.340486+00:00
-- url     : https://prove2.me/submissions/46275363-b943-4616-a917-6b5207799f7a

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {y z : ℕ} {𝒜 : Finset (Finset ℕ)} {A : Finset ℕ} (hA : A ∈ 𝒜) :
    shiftSet y z A ∈ sh y z 𝒜 := by
  rw [← compress_eq]; exact UV.compress_mem_compression hA
end HiltonMilner
