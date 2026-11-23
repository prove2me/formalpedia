-- Prove2me | solution 1 for Mdp.DiscountedMDP.numIters_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:39:52.943873+00:00
-- url     : https://prove2.me/submissions/f423df07-0650-4273-9455-56f11a4582ce

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_ValueIterationAlgorithm

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)
namespace Mdp.DiscountedMDP
theorem _root_.solution {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    M.stopCond eps v (M.numIters heps v) :=
  @Nat.find_spec _ (Classical.decPred _) (M.exists_stopCond heps v)
end Mdp.DiscountedMDP
