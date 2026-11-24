-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.vecMul_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:38:27.70036+00:00
-- url     : https://prove2.me/submissions/e84837e4-fa73-4d38-8153-973067432200

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vec_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_sum_smul_blockVector
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vecMul_blockMatrix
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


attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_last
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_last

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertSpan
variable {L : Type} [Field L] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertSpan
theorem _root_.solution (q : Fin (N + 2) → L) (g₀ U V C : Matrix (Fin N) (Fin N) L) (r b : Fin N → L) (c y z : L)
    (hy : y ≠ 0) (e : C * (U + V * g₀) = 1) :
    vec3 (0 : L) (z • (r ᵥ* C)) (z * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) ᵥ*
      mat3 q (fun k => vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k)) (vec3 (0 : L) 0 y) =
      vec3 (0 : L) (z • r) (z * c) := by
  rw [vecMul_blockMatrix]
  simp only [blockVector_first, blockVector_middle, blockVector_last, zero_smul, zero_add]
  rw [sum_smul_blockVector (z • (r ᵥ* C)) (U + V * g₀) ((V * g₀) *ᵥ b)]
  have e1 : (z • (r ᵥ* C)) ᵥ* (U + V * g₀) = z • r := by
    rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, e, Matrix.vecMul_one]
  have e2 : (z • (r ᵥ* C)) ⬝ᵥ ((V * g₀) *ᵥ b) = z * (r ⬝ᵥ ((C * V * g₀) *ᵥ b)) := by
    rw [smul_dotProduct, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, smul_eq_mul, Matrix.mul_assoc C V g₀]
  rw [e1, e2]
  exact vec_ext (by simp) (fun j => by simp) (by simp; field_simp; ring)
end GlobalTheory.CompanionTheory.InertSpan
