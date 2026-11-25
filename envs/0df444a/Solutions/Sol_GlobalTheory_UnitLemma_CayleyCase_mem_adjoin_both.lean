-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.mem_adjoin_both
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:19.249904+00:00
-- url     : https://prove2.me/submissions/bc6f70de-2556-4d53-8e80-8b174f958c0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_sub_inv_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A) (s ε : O) (Q : O[X])
    (hQm : Q.Monic) (hQ : aeval g Q = 0) (hQs : IsUnit (Q.eval (-s))) (hs : IsUnit s) (hε : IsUnit ε)
    (h2 : IsUnit (2 : O))
    (hY : Y * (g + algebraMap O A s) = algebraMap O A ε * (g - algebraMap O A s)) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by
  constructor
  · obtain ⟨w, hw, hgw⟩ := sub_inv_mem g (-s) Q hQ hQs
    rw [map_neg, sub_neg_eq_add] at hgw
    have e : Y = algebraMap O A ε * (g - algebraMap O A s) * w := by
      linear_combination (-Y) * hgw + w * hY
    rw [e]
    exact mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _)
      (sub_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _))) hw
  · set n := Q.natDegree
    let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (C s * (C ε + X)) ^ i * (C ε - X) ^ (n - i)
    have hgY : g * (algebraMap O A ε - Y) = algebraMap O A s * (algebraMap O A ε + Y) := by
      linear_combination (-1 : A) * hY
    have hR : aeval Y R = 0 := by
      have : aeval Y R = (algebraMap O A ε - Y) ^ n * aeval g Q := by
        conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
        simp only [R, map_sum, map_mul, map_pow, aeval_C, map_add, map_sub, aeval_X]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [← hgY, mul_pow, Algebra.smul_def]
        have : (algebraMap O A ε - Y) ^ n = (algebraMap O A ε - Y) ^ i * (algebraMap O A ε - Y) ^ (n - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hin]
        rw [this]; ring
      rw [this, hQ, mul_zero]
    have hRe : R.eval ε = (s * (ε + ε)) ^ n := by
      simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_sub, eval_X, sub_self]
      rw [Finset.sum_eq_single n]
      · simp [n, hQm.coeff_natDegree]
      · intro i hi hin
        have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
        rw [zero_pow this.ne', mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
    have hRu : IsUnit (R.eval ε) := by
      rw [hRe, ← two_mul]
      exact (hs.mul (h2.mul hε)).pow _
    obtain ⟨v, hv, hYv⟩ := sub_inv_mem Y ε R hR hRu
    have e : g = -(algebraMap O A s * (algebraMap O A ε + Y)) * v := by
      linear_combination (-g) * hYv - v * hgY
    rw [e]
    exact mul_mem (neg_mem (mul_mem (Subalgebra.algebraMap_mem _ _)
      (add_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)))) hv
end GlobalTheory.UnitLemma.CayleyCase
