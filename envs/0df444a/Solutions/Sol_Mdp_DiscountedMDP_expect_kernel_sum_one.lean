-- Prove2me | solution 1 for Mdp.DiscountedMDP.expect_kernel_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:25.907487+00:00
-- url     : https://prove2.me/submissions/98a07510-170e-417f-b549-0e2077157140

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution (s : S) (a : A) :
    ∑ s' : S, (M.K s a s').toReal = 1 := by
  have h1 : ∑' s' : S, M.K s a s' = 1 := (M.K s a).tsum_coe
  have h2 : ∑' s' : S, M.K s a s' = ∑ s' : S, M.K s a s' := tsum_fintype _
  have h3 : (∑ s' : S, M.K s a s').toReal = ∑ s' : S, (M.K s a s').toReal :=
    ENNReal.toReal_sum fun s' _ => PMF.apply_ne_top (M.K s a) s'
  rw [← h3, ← h2, h1, ENNReal.toReal_one]
end Mdp.DiscountedMDP
