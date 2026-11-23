-- Prove2me | solution 1 for Mdp.DiscountedMDP.contractingWith_bellman
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:28:14.144788+00:00
-- url     : https://prove2.me/submissions/2fb081db-28b3-44b9-8970-7b68ecbb956a

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic
import Theorems.Thm_Mdp_DiscountedMDP_lipschitzWith_bellman

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution : ContractingWith M.lNN M.bellman :=
  ⟨by exact_mod_cast M.l_lt_one, M.lipschitzWith_bellman⟩
end Mdp.DiscountedMDP
