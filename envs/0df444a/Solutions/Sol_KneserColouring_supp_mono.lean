-- Prove2me | solution 1 for KneserColouring.supp_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:19.911878+00:00
-- url     : https://prove2.me/submissions/e2d5d817-7282-460b-89ae-697ccb4d40fe

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}
variable {x y : Fin n → SignType} (hxy : ∀ i, x i ≠ 0 → x i = y i)
include hxy
namespace KneserColouring
theorem _root_.solution : univ.filter (fun i => x i ≠ 0) ⊆ univ.filter (fun i => y i ≠ 0) := by
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  rw [← hxy i hi]
  exact hi
end KneserColouring
