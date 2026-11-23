-- Prove2me | solution 1 for Mdp.DiscountedMDP.bellman_apriori_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:45:15.0147+00:00
-- url     : https://prove2.me/submissions/055ea61c-d85f-4bb4-b908-ced319268c72

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
theorem _root_.solution (v : S → ℝ) (n : ℕ) :
    dist (M.bellman^[n] v) M.vOpt ≤ dist v (M.bellman v) * (M.lNN : ℝ) ^ n / (1 - M.lNN) :=
  M.contractingWith_bellman.apriori_dist_iterate_fixedPoint_le v n
end Mdp.DiscountedMDP
