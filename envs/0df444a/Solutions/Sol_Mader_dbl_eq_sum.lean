-- Prove2me | solution 1 for Mader.dbl_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:46.681485+00:00
-- url     : https://prove2.me/submissions/1903fce7-6556-474f-a2b9-34d31d8ff80b

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)
namespace Mader
theorem _root_.solution (S : Finset V) : dbl G S = ∑ v ∈ S, ndeg G S v := by
  classical
  unfold dbl ndeg
  rw [Finset.card_filter, Finset.sum_product]
  refine sum_congr rfl fun v _ => ?_
  rw [Finset.card_filter]
end Mader
