-- Prove2me | solution 1 for HiltonMilner.card_union_lt_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:55:13.741648+00:00
-- url     : https://prove2.me/submissions/5a0db0e3-5f99-474f-82cb-eba48a339ffe

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {A B X : Finset ℕ} {a z : ℕ} (hA : #A = a) (hB : #B = a)
    (hzA : z ∈ A) (hzB : z ∈ B) (hX : 2 * a ≤ #X) : #(A ∪ B) < #X := by
  have h1 := card_union_add_card_inter A B
  have h2 : 0 < #(A ∩ B) := card_pos.2 ⟨z, mem_inter.2 ⟨hzA, hzB⟩⟩
  omega
end HiltonMilner
