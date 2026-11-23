-- Prove2me | solution 1 for Mdp.DiscountedMDP.lipschitzWith_bellman
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:16.333365+00:00
-- url     : https://prove2.me/submissions/9d5e907a-8134-4f23-9e17-78b59af88f8c

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic
import Theorems.Thm_Mdp_DiscountedMDP_bellman_contracting

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution : LipschitzWith M.lNN M.bellman :=
  LipschitzWith.of_dist_le_mul fun v u => M.bellman_contracting v u
end Mdp.DiscountedMDP
