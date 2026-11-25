-- Prove2me | solution 1 for HiltonMilner.wt_shift_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:06:16.192984+00:00
-- url     : https://prove2.me/submissions/17b7dad7-d54f-4686-9e3b-9b1bb4504d23

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {y z : ℕ} (hyz : y < z) {A : Finset ℕ} (hyA : y ∉ A) (hzA : z ∈ A) :
    wt (insert y (A.erase z)) < wt A := by
  unfold wt
  rw [sum_insert (fun h => hyA (mem_of_mem_erase h))]
  have := add_sum_erase A (fun x => x) hzA
  omega
end HiltonMilner
