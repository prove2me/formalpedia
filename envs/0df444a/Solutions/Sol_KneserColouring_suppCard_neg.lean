-- Prove2me | solution 1 for KneserColouring.suppCard_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:55:02.05972+00:00
-- url     : https://prove2.me/submissions/6a84a53e-8302-4aa3-87c5-c926d5fe730f

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
public import Theorems.Thm_KneserColouring_signType_neg_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
namespace KneserColouring
theorem _root_.solution (x : Fin n → SignType) : suppCard (-x) = suppCard x := by
  unfold suppCard
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, Pi.neg_apply]
  exact signType_neg_ne_zero _
end KneserColouring
