-- Prove2me | solution 1 for GlobalTheory.large_prime_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:57.924775+00:00
-- url     : https://prove2.me/submissions/0cef44f5-dd66-4c5f-b1ff-ade9297edcc6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeomIccOneLeTwoMulSub
import Theorems.Thm_GlobalTheory_primePowerSum_le_two_mul_log_div

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
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.SizeSpLarge :=
  fun x hx p hp _ => primePowerSum_le_two_mul_log_div x hx p hp
end GlobalTheory
