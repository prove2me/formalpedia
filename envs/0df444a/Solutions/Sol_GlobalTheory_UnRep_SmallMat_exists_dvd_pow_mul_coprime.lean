-- Prove2me | solution 1 for GlobalTheory.UnRep.SmallMat.exists_dvd_pow_mul_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:44:57.632275+00:00
-- url     : https://prove2.me/submissions/b1529cfd-4699-410f-a6e2-7c7608d93dd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SmallMat
open GlobalTheory.AdLat.Translate
namespace GlobalTheory.UnRep.SmallMat
theorem _root_.solution (N m : ℕ) (hm : m ≠ 0) :
    ∃ t k : ℕ, t.Coprime N ∧ m ∣ N ^ k * t := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one => exact ⟨1, 0, by simp, by simp⟩
  | prime_mul p a hp ih =>
    obtain ⟨t, k, ht, h⟩ := ih (right_ne_zero_of_mul hm)
    by_cases hpN : p ∣ N
    · refine ⟨t, k + 1, ht, ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_dvd_mul hpN h
    · refine ⟨p * t, k, Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN) ht, ?_⟩
      rw [mul_left_comm]
      exact mul_dvd_mul_left p h
end GlobalTheory.UnRep.SmallMat
