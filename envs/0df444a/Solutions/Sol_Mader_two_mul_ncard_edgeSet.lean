-- Prove2me | solution 1 for Mader.two_mul_ncard_edgeSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:37.429388+00:00
-- url     : https://prove2.me/submissions/821ad0b4-1f2d-4044-b9b9-4ba66de7163d

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
open Classical
namespace Mader
theorem _root_.solution {W : Type*} [Fintype W] (G' : SimpleGraph W) :
    2 * G'.edgeSet.ncard = ∑ v, G'.degree v := by
  classical
  rw [sum_degrees_eq_twice_card_edges, Set.ncard_eq_toFinset_card']
  rfl
end Mader
