-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_cycl_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:17.743742+00:00
-- url     : https://prove2.me/submissions/2e7c8277-27a3-4528-8f40-5e8e18ccb923

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cycl_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mul_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sum
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {i : ℕ} (hi : i < p) :
    normTrace (cycl p k) ((ζ - 1) ^ i) = (-1) ^ i := by
  have hpr := (Fact.out : p.Prime)
  rw [sub_eq_add_neg, add_pow, normTrace_sum]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    exact normTrace_of_mem _ (pow_mem (neg_mem (one_mem _)) _)
  · intro j hj hj0
    have hjp : j < p := lt_of_lt_of_le (Finset.mem_range.1 hj) (by omega)
    have hmem : (-1 : PadicAlgCl p) ^ (i - j) * (i.choose j : PadicAlgCl p) ∈ cycl p k :=
      mul_mem (pow_mem (neg_mem (one_mem _)) _) (IntermediateField.natCast_mem _ _)
    rw [mul_assoc, mul_comm, normTrace_mul_of_mem _ hmem]
    have hcop : j.Coprime (p ^ (k + 1)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpr).2
        fun h => by have := Nat.le_of_dvd (by omega) h; omega))
    rw [normTrace_cycl_isPrimitiveRoot hk (hζ.pow_of_coprime j hcop), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos i)) h
end GroundTheory.PAdicHodge
