-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLevi.gram_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:25:58.384961+00:00
-- url     : https://prove2.me/submissions/0601fef3-50fa-44b6-8eef-7d0b672c7430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExists
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_mid
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_last
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
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
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ M * antiJ L n * M) i j = ∑ k, σ (M k i) * M k.rev j := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, antiJ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k.rev]
  · rw [if_pos (by have := k.isLt; simp only [Fin.val_rev]; omega), mul_one]
  · intro l _ hl
    rw [if_neg, mul_zero, zero_mul]
    intro h
    apply hl
    ext
    have := k.isLt
    have := l.isLt
    simp only [Fin.val_rev]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h
end GlobalTheory.CompanionTheory.InertLevi
