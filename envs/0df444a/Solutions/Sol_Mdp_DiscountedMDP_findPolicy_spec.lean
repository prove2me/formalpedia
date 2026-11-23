-- Prove2me | solution 1 for Mdp.DiscountedMDP.findPolicy_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:33:59.927581+00:00
-- url     : https://prove2.me/submissions/5f107010-a3da-41d7-9290-a1f266b229dd

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (v : S → ℝ) (s : S) (a' : A) :
    M.r s a' + M.l * M.expect s a' v
      ≤ M.r s (M.findPolicy v s) + M.l * M.expect s (M.findPolicy v s) v :=
  (M.exists_argmax v s).choose_spec.2 a' (Finset.mem_univ a')
end Mdp.DiscountedMDP
