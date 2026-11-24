-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLevi.aTerm_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:05:54.509416+00:00
-- url     : https://prove2.me/submissions/d7ba7dc0-a6cc-41eb-a6ea-8987f91bd28d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_RecursionIdentity
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
noncomputable section
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLevi
namespace GlobalTheory.CompanionTheory.InertLevi
theorem _root_.solution {q N : ℕ} {X α : ℂ} (k : ℕ) :
    aTerm q N X α (-((k : ℤ) + 1)) = ((q : ℂ) ^ (N + 1) * X / α) * ((q : ℂ) ^ (N + 1) * X / α) ^ k := by
  have h : (q : ℂ) ^ (-(-((k : ℤ) + 1)) * ((N : ℤ) + 1)) = (q : ℂ) ^ ((N + 1) * (k + 1)) := by
    rw [← zpow_natCast]
    congr 1
    push_cast
    ring
  have h1 : (-((k : ℤ) + 1)).toNat = 0 := by omega
  have h2 : (-((k : ℤ) + 1)).natAbs = k + 1 := by omega
  have h3 : α ^ (-((k : ℤ) + 1)) = (α ^ (k + 1))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rw [aTerm, h, h1, h2, h3, ← pow_succ', div_pow, mul_pow, ← pow_mul]
  simp only [mul_zero, pow_zero, one_mul, div_eq_mul_inv]
  ring
end GlobalTheory.CompanionTheory.InertLevi
