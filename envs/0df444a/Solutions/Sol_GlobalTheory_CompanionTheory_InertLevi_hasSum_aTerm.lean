-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLevi.hasSum_aTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:16.362824+00:00
-- url     : https://prove2.me/submissions/7de6b3b8-1200-401f-b5c4-09f392cf94eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_RecursionIdentity
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_aTerm_nat
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_aTerm_neg
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
theorem _root_.solution {q N : ℕ} {X α : ℂ} (hq : (q : ℂ) ≠ 0) (h1 : ‖(q : ℂ) ^ (N + 1) * X * α‖ < 1)
    (h2 : ‖(q : ℂ) ^ (N + 1) * X / α‖ < 1) :
    HasSum (aTerm q N X α) ((1 - (q : ℂ) ^ (N + 1) * X * α)⁻¹ +
      ((q : ℂ) ^ (N + 1) * X / α) * (1 - (q : ℂ) ^ (N + 1) * X / α)⁻¹) := by
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · simp only [aTerm_nat hq]
    exact hasSum_geometric_of_norm_lt_one h1
  · simp only [aTerm_neg]
    exact (hasSum_geometric_of_norm_lt_one h2).mul_left _
end GlobalTheory.CompanionTheory.InertLevi
