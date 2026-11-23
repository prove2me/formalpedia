-- Prove2me | solution 1 for Mdp.DiscountedMDP.policy_iteration_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:45:49.308587+00:00
-- url     : https://prove2.me/submissions/3d18283c-0d1e-4c84-a128-239b94b6a2cf

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_PolicyIteration
import Theorems.Thm_Mdp_DiscountedMDP_policyIteration_isFixedPt
import Theorems.Thm_Mdp_DiscountedMDP_policyStep_fixedPoint_value_eq_vOpt

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (d : S → A) : M.value (M.policyIteration d) = M.vOpt :=
  M.policyStep_fixedPoint_value_eq_vOpt (M.policyIteration d) (M.policyIteration_isFixedPt d)
end Mdp.DiscountedMDP
