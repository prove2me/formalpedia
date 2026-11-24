-- Prove2me | solution 1 for GlobalTheory.parsevalSep_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:31.43292+00:00
-- url     : https://prove2.me/submissions/ec7c8680-3254-4ba1-9cc1-048c29e042d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParsevalBoundIntegerVectorSmallFourierSupport
import Theorems.Thm_GlobalTheory_parsevalSep_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N)
    (c : ℕ → ℤ) :
    ∑ j ∈ Finset.range N, ‖∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k)‖ ^ 2
      = (N : ℝ) * ((∑ k ∈ Finset.range N, c k ^ 2 : ℤ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, map_mul, map_pow, map_intCast]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  have : ∀ l ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
      = if k = l then (c k : ℂ) * c l * N else 0 := by
    intro l hl
    have := parsevalSep_orth N ω hN hω k l (Finset.mem_range.1 hk) (Finset.mem_range.1 hl)
    have e : ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
       = (c k : ℂ) * c l * ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, this]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hk]
  ring
end GlobalTheory
