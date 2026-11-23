-- Prove2me | solution 1 for Mdp.DiscountedMDP.policyIteration_isFixedPt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:41:29.313017+00:00
-- url     : https://prove2.me/submissions/3b68bd44-d930-419c-800b-486bf440464b

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_PolicyIteration
import Theorems.Thm_Mdp_DiscountedMDP_policyIterNum_spec

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (d : S → A) :
    M.policyStep (M.policyIteration d) = M.policyIteration d :=
  M.policyIterNum_spec d
end Mdp.DiscountedMDP
