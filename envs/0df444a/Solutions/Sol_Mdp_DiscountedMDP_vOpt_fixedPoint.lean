-- Prove2me | solution 1 for Mdp.DiscountedMDP.vOpt_fixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:32:32.988385+00:00
-- url     : https://prove2.me/submissions/59281617-bf34-416b-8bae-64ed5b48b08c

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
import Theorems.Thm_Mdp_DiscountedMDP_contractingWith_bellman


set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution : M.bellman M.vOpt = M.vOpt :=
  M.contractingWith_bellman.fixedPoint_isFixedPt
end Mdp.DiscountedMDP
