-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.v_det_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:49.620061+00:00
-- url     : https://prove2.me/submissions/20b5c7e4-ae65-409e-bf0d-a756a5454d9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex
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



set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (e l : ℕ) {C : Matrix (Fin N) (Fin N) L}
    (hdet : Valued.v C.det = WithZero.exp (-(l : ℤ))) :
    Valued.v (ϖ ^ e • C).det = WithZero.exp (-((l + N * e : ℕ) : ℤ)) := by
  rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, map_pow, hϖ, hdet, ← pow_mul,
    ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1
  push_cast
  simp only [nsmul_eq_mul]
  push_cast
  ring
end GlobalTheory.CompanionTheory.InertCount
