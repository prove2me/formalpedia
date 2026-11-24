-- Prove2me | solution 1 for Mader.dbl_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:04.648544+00:00
-- url     : https://prove2.me/submissions/77d28173-33b8-460b-a6af-74ed22735dce

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
public import Theorems.Thm_Mader_dbl_eq_sum
public import Theorems.Thm_Mader_two_mul_ncard_edgeSet

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)
open Classical
namespace Mader
theorem _root_.solution [Fintype V] : dbl G univ = 2 * G.edgeSet.ncard := by
  classical
  rw [two_mul_ncard_edgeSet, dbl_eq_sum]
  refine sum_congr rfl (fun v _ => ?_)
  unfold ndeg
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
end Mader
