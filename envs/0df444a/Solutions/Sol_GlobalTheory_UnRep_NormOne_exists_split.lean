-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:57.57778+00:00
-- url     : https://prove2.me/submissions/9f9d71e6-609e-4b0a-8228-b8db2b6322bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
namespace GlobalTheory.UnRep.NormOne
theorem _root_.solution (N : ℕ) : ∀ M : ℕ, 0 < M → ∃ D₁ D₂ k : ℕ, M = D₁ * D₂ ∧ D₁ ∣ N ^ k ∧ D₂.Coprime N := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM
    by_cases h : M.Coprime N
    · exact ⟨1, M, 0, by simp, by simp, h⟩
    · obtain ⟨M', hM'⟩ := Nat.gcd_dvd_left M N
      have hg : 0 < Nat.gcd M N := Nat.gcd_pos_of_pos_left N hM
      have hg1 : Nat.gcd M N ≠ 1 := h
      have hpos : 0 < M' := by
        rcases Nat.eq_zero_or_pos M' with h0 | h0
        · rw [h0, mul_zero] at hM'; omega
        · exact h0
      have hlt : M' < M := by
        have h2 : 2 ≤ Nat.gcd M N := by omega
        nlinarith
      obtain ⟨D₁, D₂, k, h1, h2, h3⟩ := ih M' hlt hpos
      refine ⟨Nat.gcd M N * D₁, D₂, k + 1, by rw [mul_assoc, ← h1]; exact hM', ?_, h3⟩
      rw [pow_succ']
      exact Nat.mul_dvd_mul (Nat.gcd_dvd_right M N) h2
end GlobalTheory.UnRep.NormOne
