-- Prove2me | solution 1 for Mdp.DiscountedMDP.abs_expect_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:23:45.311483+00:00
-- url     : https://prove2.me/submissions/99a60771-4f9f-4f82-9dbf-d08383d6d969

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic
import Theorems.Thm_Mdp_DiscountedMDP_expect_kernel_sum_one

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (s : S) (a : A) (v u : S → ℝ) :
    |M.expect s a v - M.expect s a u| ≤ dist v u := by
  have hrw : M.expect s a v - M.expect s a u
      = ∑ s' : S, (M.K s a s').toReal * (v s' - u s') := by
    simp only [expect, ← Finset.sum_sub_distrib]
    congr 1; ext s'; ring
  rw [hrw]
  calc |∑ s' : S, (M.K s a s').toReal * (v s' - u s')|
      ≤ ∑ s' : S, |(M.K s a s').toReal * (v s' - u s')| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s' : S, (M.K s a s').toReal * |v s' - u s'| := by
        simp [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ s' : S, (M.K s a s').toReal * dist v u := by
        apply Finset.sum_le_sum
        intro s' _
        have hv : |v s' - u s'| ≤ dist v u := by
          rw [← Real.dist_eq]
          exact dist_le_pi_dist v u s'
        exact mul_le_mul_of_nonneg_left hv ENNReal.toReal_nonneg
    _ = dist v u := by rw [← Finset.sum_mul, M.expect_kernel_sum_one s a, one_mul]
end Mdp.DiscountedMDP
