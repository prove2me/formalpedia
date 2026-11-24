-- Prove2me | solution 1 for GlobalTheory.geom_Icc_one_le_two_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:12.688442+00:00
-- url     : https://prove2.me/submissions/1c817c9e-e18a-4a99-91d2-43567791afe8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeomIccOneLeTwoMulSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (N : ℕ) :
    ∑ i ∈ Icc 1 N, r ^ i ≤ 2 * r - 2 * r ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hp : 0 ≤ r ^ (n + 1) := pow_nonneg h0 _
    have : r ^ (n + 1 + 1) = r ^ (n + 1) * r := pow_succ _ _
    nlinarith
end GlobalTheory
