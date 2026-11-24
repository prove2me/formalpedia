-- Prove2me | solution 1 for GlobalTheory.csr_reverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:55.627192+00:00
-- url     : https://prove2.me/submissions/c6b219e3-2514-4b6d-90e9-5dde56b09e7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalOrthogonalRangeUnitarySelfReciprocal
import Theorems.Thm_GlobalTheory_csr_pow_mul_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (γ B : Matrix (Fin n) (Fin n) K)
    (h : γ * B = 1) (P : K[X]) :
    γ ^ P.natDegree * aeval B P = aeval γ P.reverse := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range' (n := P.natDegree + 1), Finset.mul_sum]
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : P.natDegree + 1 - 1 - i = P.natDegree - i := by omega
    rw [e1, mul_smul_comm, csr_pow_mul_pow γ B h _ _ (Nat.sub_le _ _), coeff_reverse,
      revAt_le hi']
    have e2 : P.natDegree - (P.natDegree - i) = i := by omega
    rw [e2]
  · exact Nat.lt_succ_of_le (reverse_natDegree_le P)
end GlobalTheory
