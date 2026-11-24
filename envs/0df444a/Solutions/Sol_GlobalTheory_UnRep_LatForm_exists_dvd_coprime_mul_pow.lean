-- Prove2me | solution 1 for GlobalTheory.UnRep.LatForm.exists_dvd_coprime_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:27.114257+00:00
-- url     : https://prove2.me/submissions/80359239-e3ef-49ff-8268-7c2204596ebb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator
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
theorem _root_.solution (N : ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ j u : ℕ, u.Coprime N ∧ m ∣ u * N ^ j := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h : Nat.gcd m N = 1
    · exact ⟨0, m, h, by simp⟩
    · obtain ⟨m', hm'⟩ := Nat.gcd_dvd_left m N
      have hg : 0 < Nat.gcd m N := Nat.gcd_pos_of_pos_left _ hm
      have hm'0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm'; omega)
      have hlt : m' < m := by
        have : 2 ≤ Nat.gcd m N := by omega
        nlinarith
      obtain ⟨j, u, hu, hd⟩ := ih m' hlt hm'0
      refine ⟨j + 1, u, hu, ?_⟩
      rw [hm', pow_succ, ← mul_assoc, mul_comm (Nat.gcd m N)]
      exact Nat.mul_dvd_mul hd (Nat.gcd_dvd_right m N)
end GlobalTheory.UnRep.LatForm
