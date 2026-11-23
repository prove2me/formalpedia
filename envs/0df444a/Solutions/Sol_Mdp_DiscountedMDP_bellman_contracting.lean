-- Prove2me | solution 1 for Mdp.DiscountedMDP.bellman_contracting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:25:35.962896+00:00
-- url     : https://prove2.me/submissions/2e164c97-1afa-4b86-ba05-fb4610804cea

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic
import Theorems.Thm_P2M_Mdp_abs_sup__sub_sup__le_dbc2ecd51cdd
import Theorems.Thm_Mdp_DiscountedMDP_abs_expect_sub_le

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (v u : S → ℝ) :
    dist (M.bellman v) (M.bellman u) ≤ M.l * dist v u := by
  rw [dist_pi_le_iff (mul_nonneg M.l_nonneg dist_nonneg)]
  intro s
  rw [Real.dist_eq]
  apply abs_sup'_sub_sup'_le _ _ _ _ _
  intro a _
  have hbound : |M.expect s a v - M.expect s a u| ≤ dist v u := M.abs_expect_sub_le s a v u
  calc |(M.r s a + M.l * M.expect s a v) - (M.r s a + M.l * M.expect s a u)|
      = M.l * |M.expect s a v - M.expect s a u| := by
        rw [show (M.r s a + M.l * M.expect s a v) - (M.r s a + M.l * M.expect s a u)
              = M.l * (M.expect s a v - M.expect s a u) from by ring,
            abs_mul, abs_of_nonneg M.l_nonneg]
    _ ≤ M.l * dist v u := mul_le_mul_of_nonneg_left hbound M.l_nonneg
end Mdp.DiscountedMDP
