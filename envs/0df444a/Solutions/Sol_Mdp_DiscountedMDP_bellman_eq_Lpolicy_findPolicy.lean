-- Prove2me | solution 1 for Mdp.DiscountedMDP.bellman_eq_Lpolicy_findPolicy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:36:15.619915+00:00
-- url     : https://prove2.me/submissions/0186ab7e-0291-4918-b8be-35464fdf960d

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
import Theorems.Thm_Mdp_DiscountedMDP_findPolicy_spec

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (v : S → ℝ) (s : S) :
    M.bellman v s = M.Lpolicy (M.findPolicy v) v s := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    exact M.findPolicy_spec v s a
  · exact Finset.le_sup' (fun a => M.r s a + M.l * M.expect s a v)
      (Finset.mem_univ (M.findPolicy v s))
end Mdp.DiscountedMDP
