-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLevi.blkMat_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:54.015279+00:00
-- url     : https://prove2.me/submissions/59616c2e-6e56-4a29-b55a-43851bed44e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExists
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_mid
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_gram_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_mid_rev
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


attribute [local simp] GlobalTheory.CompanionTheory.InertLevi.edge_zero
attribute [local simp] GlobalTheory.CompanionTheory.InertLevi.edge_mid
attribute [local simp] GlobalTheory.CompanionTheory.InertLevi.edge_last

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLevi
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertLevi
theorem _root_.solution {x y : L} (hxy : σ x * y = 1) (hyx : σ y * x = 1) {A : Matrix (Fin N) (Fin N) L}
    (hA : cT σ A * antiJ L N * A = antiJ L N) :
    cT σ (blkMat x y A) * antiJ L (N + 2) * blkMat x y A = antiJ L (N + 2) := by
  ext i j
  rw [gram_apply, sum_idx]
  simp only [Fin.rev_last, ← mid_rev, Fin.rev_zero]
  rcases idx_cases i with rfl | ⟨r, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨s, rfl⟩ | rfl
  · simp [blkMat, antiJ]
  · simp [blkMat, antiJ, val_mid, s.isLt.ne]
  · simp [blkMat, antiJ, hxy]
  · simp [blkMat, antiJ, val_mid, r.isLt.ne]
  · have h := congrFun (congrFun hA r) s
    rw [gram_apply] at h
    simp only [blkMat, edge_zero, edge_mid, edge_last, map_zero, zero_mul, mul_zero, zero_add, add_zero]
    rw [h]
    simp only [antiJ]
    have e1 := val_mid r
    have e2 := val_mid s
    by_cases h1 : (r : ℕ) + s + 1 = N
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  · simp [blkMat, antiJ, val_mid]
  · simp [blkMat, antiJ, hyx]
  · simp [blkMat, antiJ, val_mid]
  · simp [blkMat, antiJ]
end GlobalTheory.CompanionTheory.InertLevi
