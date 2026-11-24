-- Prove2me | solution 1 for GlobalTheory.exists_nat_trace_of_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:36.218382+00:00
-- url     : https://prove2.me/submissions/a6479731-2e0a-4363-8410-bf78071f86a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_exists_nat_trace_of_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [Fintype A] [DecidableEq A]
namespace GlobalTheory
theorem _root_.solution {V : Matrix A A ℂ} (hV : V ^ 4 = 1) :
    ∃ r : ℕ, (Fintype.card A : ℂ) + V.trace + (V ^ 2).trace + (V ^ 3).trace = 4 * r := by
  set S : Matrix A A ℂ := 1 + V + V ^ 2 + V ^ 3 with hS
  have h1 : V * S = S := by
    have : V * S = V + V ^ 2 + V ^ 3 + V ^ 4 := by rw [hS]; noncomm_ring
    rw [this, hV, hS]; abel
  have h2 : V ^ 2 * S = S := by rw [pow_two, mul_assoc, h1, h1]
  have h3 : V ^ 3 * S = S := by rw [pow_succ, mul_assoc, h1, h2]
  have h4 : S * S = (4 : ℂ) • S := by
    conv_lhs => rw [hS, add_mul, add_mul, add_mul, ← hS, one_mul, h1, h2, h3]
    module
  obtain ⟨r, hr⟩ := exists_nat_trace_of_mul_self (E := (4 : ℂ)⁻¹ • S) (by
    rw [smul_mul_smul_comm, h4, smul_smul]; norm_num)
  refine ⟨r, ?_⟩
  rw [← hr, hS]
  simp only [trace_smul, trace_add, trace_one, smul_eq_mul]
  ring
end GlobalTheory
