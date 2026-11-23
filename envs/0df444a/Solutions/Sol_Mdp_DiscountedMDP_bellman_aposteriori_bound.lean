-- Prove2me | solution 1 for Mdp.DiscountedMDP.bellman_aposteriori_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:33:27.767717+00:00
-- url     : https://prove2.me/submissions/147e8811-a7bd-48f9-b615-084ae2501b5d

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
    dist (M.bellman^[n] v) M.vOpt ≤ dist (M.bellman^[n] v) (M.bellman^[n + 1] v) / (1 - M.lNN) :=
  M.contractingWith_bellman.aposteriori_dist_iterate_fixedPoint_le v n
end Mdp.DiscountedMDP
