-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CongruenceCayley.inv_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:16:21.516415+00:00
-- url     : https://prove2.me/submissions/2aabe8cb-b5e8-49cf-a8ff-386bb5a97306

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruence
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_sub_inv_mem
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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CongruenceCayley
open GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CongruenceCayley
theorem _root_.solution {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g : A) (α β : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) :
    ∃ w ∈ Algebra.adjoin O ({g} : Set A), (algebraMap O A α + algebraMap O A β * g) * w = 1 := by
  obtain ⟨Q, hQm, hQ⟩ := hg
  rw [← aeval_def] at hQ
  set D := algebraMap O A α + algebraMap O A β * g with hD
  set n := Q.natDegree
  let R : O[X] := ∑ i ∈ Finset.range (n + 1), C (Q.coeff i) * (X - C α) ^ i * C β ^ (n - i)
  have hR : aeval D R = 0 := by
    have : aeval D R = algebraMap O A β ^ n * aeval g Q := by
      conv_rhs => rw [aeval_eq_sum_range, Finset.mul_sum]
      simp only [R, map_sum, map_mul, map_pow, aeval_C, map_sub, aeval_X]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Algebra.smul_def, hD]
      have : algebraMap O A β ^ n = algebraMap O A β ^ i * algebraMap O A β ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hin]
      rw [this]; ring
    rw [this, hQ, mul_zero]
  have hR0 : IsUnit (R.eval 0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hb : IsLocalRing.residue O β = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hβ
    have ha : IsLocalRing.residue O α ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hα
    simp only [R, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, map_sum, map_mul, map_pow,
      map_sub, map_zero, hb]
    rw [Finset.sum_eq_single n]
    · simp [n, hQm.coeff_natDegree, ha]
    · intro i hi hin
      have : 0 < n - i := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hin)
      rw [zero_pow this.ne', mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  obtain ⟨w, hw, hDw⟩ := sub_inv_mem D 0 R hR hR0
  rw [map_zero, sub_zero] at hDw
  refine ⟨w, ?_, hDw⟩
  have hDmem : D ∈ Algebra.adjoin O ({g} : Set A) :=
    add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl))
  exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hDmem) hw
end GlobalTheory.UnitLemma.CongruenceCayley
