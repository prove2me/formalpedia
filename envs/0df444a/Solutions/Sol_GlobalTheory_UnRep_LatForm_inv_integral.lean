-- Prove2me | solution 1 for GlobalTheory.UnRep.LatForm.inv_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:08.249059+00:00
-- url     : https://prove2.me/submissions/3d13f003-2ff8-405b-9fb5-03a90d65cee1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator
import Theorems.Thm_GlobalTheory_UnRep_LatForm_exists_dvd_coprime_mul_pow
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
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.LatForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.UnRep.LatForm
theorem _root_.solution {V : Type} [AddCommGroup V] (Λ : AddSubgroup V) (k k' : V →+ V)
    (hk : ∀ z, k' (k z) = z) (N t m : ℕ) (ht : t.Coprime N) (hm : 0 < m)
    (h1 : ∀ z ∈ Λ, ∃ w ∈ Λ, t • (k z - z) = N • w) (h2 : ∀ z ∈ Λ, m • k' z ∈ Λ) :
    ∃ t' : ℕ, t'.Coprime N ∧ ∀ z ∈ Λ, t' • k' z ∈ Λ := by
  have key : ∀ j : ℕ, ∀ z ∈ Λ, ∃ y ∈ Λ, ∃ w ∈ Λ, t ^ j • k' z = y + N ^ j • k' w := by
    intro j
    induction j with
    | zero => intro z hz; exact ⟨0, Λ.zero_mem, z, hz, by simp⟩
    | succ j ih =>
      intro z hz
      obtain ⟨y, hy, w, hw, e⟩ := ih z hz
      obtain ⟨w', hw', e'⟩ := h1 w hw
      have e2 : t • k' w = t • w + N • k' (-w') := by
        have := congrArg k' e'
        rw [map_nsmul, map_nsmul, map_sub, hk, smul_sub] at this
        rw [map_neg, smul_neg, ← this]; abel
      refine ⟨t • y + N ^ j • t • w, Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (Λ.nsmul_mem hw _) _),
        -w', Λ.neg_mem hw', ?_⟩
      rw [pow_succ', mul_smul, e, smul_add, smul_comm t (N ^ j), e2, smul_add, pow_succ, mul_smul, add_assoc]
  obtain ⟨j, u, hu, q, hq⟩ := exists_dvd_coprime_mul_pow N m hm
  refine ⟨u * t ^ j, Nat.Coprime.mul_left hu (Nat.Coprime.pow_left _ ht), fun z hz => ?_⟩
  obtain ⟨y, hy, w, hw, e⟩ := key j z hz
  rw [mul_smul, e, smul_add, ← mul_smul, hq, mul_comm, mul_smul]
  exact Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (h2 w hw) _)
end GlobalTheory.UnRep.LatForm
