-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.mid_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:22:55.814059+00:00
-- url     : https://prove2.me/submissions/cc17d251-9625-44d7-ae62-e4381e42ab0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vec3_add
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_comb
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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertSpan
theorem _root_.solution {R : Submodule (intL L) (Fin (N + 2) → L)} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
    (hf : IsFrac g₀ U V C) (hm : ∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R)
    (h1 : ∀ i, vec3 (0 : L) 0 (((C * V * g₀) *ᵥ b) i) ∈ R)
    (h2 : ∀ i, vec3 (0 : L) 0 (((g₀ * C * U) *ᵥ b) i) ∈ R) :
    (∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 ∈ R) ∧
      ∀ k, vec3 (0 : L) (g₀ k) ((g₀ *ᵥ b) k) ∈ R := by
  obtain ⟨hU, hV, hC, hgC, e⟩ := hf
  have e' : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 e
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have := R.sub_mem (comb R hC (U + V * g₀) ((V * g₀) *ᵥ b) hm k) (h1 k)
    rw [e', blockVector_sub, sub_zero, Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at this
    simpa using this
  · have := R.add_mem (comb R hgC (U + V * g₀) ((V * g₀) *ᵥ b) hm k) (h2 k)
    have e2 : g₀ * C * (U + V * g₀) = g₀ := by rw [Matrix.mul_assoc, e', Matrix.mul_one]
    have e3 : ((g₀ * C) *ᵥ ((V * g₀) *ᵥ b)) k + ((g₀ * C * U) *ᵥ b) k = (g₀ *ᵥ b) k := by
      rw [Matrix.mulVec_mulVec, ← Pi.add_apply, ← Matrix.add_mulVec, ← Matrix.mul_add, add_comm, e2]
    rwa [vec3_add, e2, add_zero, e3] at this
end GlobalTheory.CompanionTheory.InertSpan
