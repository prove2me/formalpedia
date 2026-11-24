-- Prove2me | solution 1 for GlobalTheory.InertZeta.DualLat.tw_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:16.006859+00:00
-- url     : https://prove2.me/submissions/1c0a8230-a7db-4ec9-bceb-1b4a5203d83a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DualInterEqSum
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_mulVec
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_vecMul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_inv_apply
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



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.DualLat
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.InertZeta.DualLat
theorem _root_.solution {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (g : GU σ N) (x : Fin N → L) :
    tw σ x ᵥ* mat g = tw σ (mat g⁻¹ *ᵥ x) := by
  ext j
  simp only [tw, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mat_inv_apply, hσσ, Fin.rev_rev]
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans ?_
  simp [mul_comm]
end GlobalTheory.InertZeta.DualLat
