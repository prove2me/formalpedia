-- Prove2me | solution 1 for Mdp.DiscountedMDP.exists_unique_fixedPoint_choose_eq_vOpt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:45:13.315735+00:00
-- url     : https://prove2.me/submissions/744fa6af-48c9-4d4a-bb05-d805962d39e8

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
import Theorems.Thm_Mdp_DiscountedMDP_contractingWith_bellman
import Theorems.Thm_Mdp_DiscountedMDP_exists_unique_fixedPoint


set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution :
    M.exists_unique_fixedPoint.choose = M.vOpt :=
  M.contractingWith_bellman.fixedPoint_unique M.exists_unique_fixedPoint.choose_spec.1
end Mdp.DiscountedMDP
