-- Prove2me | solution 1 for GlobalTheory.index_range_eq_card_ker_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:00:09.31281+00:00
-- url     : https://prove2.me/submissions/0a99c727-9ede-47aa-aede-ed56f9d54391

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardQuotPrimeSmulEqCardKerMulPowFinrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {D : Type} [AddCommGroup D] [Finite D] (f : D →+ D) :
    f.range.index = Nat.card f.ker := by
  have h1 := f.range.card_mul_index
  have h2 := f.ker.card_mul_index
  rw [AddSubgroup.index_ker] at h2
  have h3 : 0 < Nat.card f.range := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left h3
  rw [h1, mul_comm, h2]
end GlobalTheory
