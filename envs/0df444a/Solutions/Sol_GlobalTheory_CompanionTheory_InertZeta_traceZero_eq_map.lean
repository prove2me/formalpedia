-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.traceZero_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:05:50.919806+00:00
-- url     : https://prove2.me/submissions/c1763205-ec47-4d95-86bc-5d53524113b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceZeroIntegersModUniformizerCardOfCardSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_TraceIndexFormula
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mem_traceZero
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
open GlobalTheory.InertZeta Formalism.UG
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution {σ : L →+* L} {c : L} (hc : c ≠ 0) (hσ : σ c = c) :
    traceZero σ c =
      ((intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker).map (AddMonoidHom.mulLeft c⁻¹) := by
  ext x
  rw [mem_traceZero, AddSubgroup.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨c * x, AddSubgroup.mem_inf.2 ⟨h1, ?_⟩, by simp [hc]⟩
    rw [AddMonoidHom.mem_ker]
    show σ (c * x) + c * x = 0
    rw [map_mul, hσ, ← mul_add, h2, mul_zero]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hy
    rw [AddMonoidHom.mem_ker] at h2
    have h2' : σ y + y = 0 := h2
    have hi : σ c⁻¹ = c⁻¹ := by rw [map_inv₀, hσ]
    refine ⟨?_, ?_⟩
    · show c * (c⁻¹ * y) ∈ intL L
      rw [mul_inv_cancel_left₀ hc]
      exact h1
    · show σ (c⁻¹ * y) + c⁻¹ * y = 0
      rw [map_mul, hi, ← mul_add, h2', mul_zero]
end GlobalTheory.CompanionTheory.InertZeta
