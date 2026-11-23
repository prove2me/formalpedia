-- Prove2me | solution 1 for Mdp.DiscountedMDP.policyIterNum_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:10.819409+00:00
-- url     : https://prove2.me/submissions/07a76bde-c6d3-4fb4-965a-83e4a689ebb8

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_PolicyIteration

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (d : S → A) :
    M.policyStep ((M.policyStep)^[M.policyIterNum d] d) = (M.policyStep)^[M.policyIterNum d] d :=
  @Nat.find_spec _ (Classical.decPred _) (M.exists_policyStep_fixedPoint d)
end Mdp.DiscountedMDP
