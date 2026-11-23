-- Prove2me | solution 1 for Mdp.DiscountedMDP.policyStep_fixedPoint_value_eq_vOpt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:24.414805+00:00
-- url     : https://prove2.me/submissions/f2275d9a-be11-4c06-b26d-fd3745fc1e16

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_PolicyIteration
import Theorems.Thm_Mdp_DiscountedMDP_contractingWith_bellman
import Theorems.Thm_Mdp_DiscountedMDP_value_fixedPoint


set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (d : S → A) (hd : M.policyStep d = d) :
    M.value d = M.vOpt := by
  have h1 : M.Lpolicy (M.policyStep d) (M.value d) = M.bellman (M.value d) :=
    M.Lpolicy_policyImprove_eq_bellman d (M.value d)
  rw [hd] at h1
  have hbellman : M.bellman (M.value d) = M.value d := by
    rw [← h1]
    exact M.value_fixedPoint d
  exact M.contractingWith_bellman.fixedPoint_unique hbellman
end Mdp.DiscountedMDP
