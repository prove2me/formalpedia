-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.mul_Bm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:33.498807+00:00
-- url     : https://prove2.me/submissions/3229c806-c684-4b9d-a839-514f999c7f6c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_sum_mulVec__fc8d7b839a0b
import Theorems.Thm_GlobalTheory_JR_NormalFormL_pow_card_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (Y : Gl r k) : Y.1 * Bm Y = Bm Y * companion (inv Y).1 := by
  ext i j
  have hl : (Y.1 * Bm Y) i j = (Y.1 ^ ((j : ℕ) + 1) *ᵥ Y.2.1) i := by
    rw [pow_succ', ← mulVec_mulVec]
    simp [mul_apply, Bm, mulVec, dotProduct]
  rw [hl, mul_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · simp only [companion, of_apply, hj, if_true, Bm, inv]
    rw [pow_card_eq Y.1, neg_mulVec, sum_mulVec']
    simp only [Pi.neg_apply, Finset.sum_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun l => (Y.1 ^ l *ᵥ Y.2.1) i * -Y.1.charpoly.coeff l),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  · have hj' : (j : ℕ) + 1 < r := by omega
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj'⟩ : Fin r)]
    · simp [companion, hj, Bm]
    · intro l _ hne
      have : ¬ ((l : ℕ) = (j : ℕ) + 1) := fun h => hne (Fin.ext h)
      simp [companion, hj, this]
    · intro h; exact absurd (Finset.mem_univ _) h
end GlobalTheory.JR.NormalFormL
