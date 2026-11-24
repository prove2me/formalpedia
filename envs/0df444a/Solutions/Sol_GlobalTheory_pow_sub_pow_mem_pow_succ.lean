-- Prove2me | solution 1 for GlobalTheory.pow_sub_pow_mem_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:52.410217+00:00
-- url     : https://prove2.me/submissions/656726c3-0fc9-4021-8e69-efd391fce2f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] {I : Ideal R} {a b : R} (ha : a ∈ I)
    (hb : b ∈ I) (hab : a - b ∈ I ^ 2) (d : ℕ) : a ^ d - b ^ d ∈ I ^ (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have : a ^ (d + 1) - b ^ (d + 1) = a * (a ^ d - b ^ d) + (a - b) * b ^ d := by ring
    rw [this]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ']; exact Ideal.mul_mem_mul ha ih
    · rw [show d + 1 + 1 = 2 + d by ring, pow_add]
      exact Ideal.mul_mem_mul hab (Ideal.pow_mem_pow hb d)
end GlobalTheory
