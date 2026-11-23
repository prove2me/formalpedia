-- Prove2me | solution 1 for Mdp.DiscountedMDP.bellman_iterate_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:33:05.872022+00:00
-- url     : https://prove2.me/submissions/42f59943-8d73-4624-88d5-fe37a7e3ee87

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
theorem _root_.solution (v : S → ℝ) :
    Filter.Tendsto (fun n => M.bellman^[n] v) Filter.atTop (nhds M.vOpt) :=
  M.contractingWith_bellman.tendsto_iterate_fixedPoint v
end Mdp.DiscountedMDP
