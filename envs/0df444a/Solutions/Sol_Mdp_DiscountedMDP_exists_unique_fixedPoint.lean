-- Prove2me | solution 1 for Mdp.DiscountedMDP.exists_unique_fixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:29:35.150061+00:00
-- url     : https://prove2.me/submissions/317e036e-d419-4c91-9f32-5bc705a747dd

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic
import Theorems.Thm_Mdp_DiscountedMDP_bellman_contracting
import Theorems.Thm_Mdp_DiscountedMDP_contractingWith_bellman

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution : ∃! v : S → ℝ, M.bellman v = v := by
  obtain ⟨v, hv_fix, -, -⟩ := M.contractingWith_bellman.exists_fixedPoint 0 (edist_ne_top _ _)
  refine ⟨v, hv_fix, fun w hw_fix => ?_⟩
  by_contra hne
  have hpos : 0 < dist v w := dist_pos.mpr (Ne.symm hne)
  have hshrink : dist v w ≤ M.l * dist v w := by
    have := M.bellman_contracting v w
    rwa [hv_fix, hw_fix] at this
  nlinarith [M.l_lt_one]
end Mdp.DiscountedMDP
