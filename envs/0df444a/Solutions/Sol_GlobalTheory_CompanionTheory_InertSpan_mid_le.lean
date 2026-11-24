-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.mid_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:22:57.940093+00:00
-- url     : https://prove2.me/submissions/0978a26d-fc60-4b96-bfbf-725efe6f4bdb

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
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_isInt_one
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
    (hf : IsFrac g₀ U V C) (h1 : ∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 ∈ R)
    (h2 : ∀ k, vec3 (0 : L) (g₀ k) ((g₀ *ᵥ b) k) ∈ R) :
    (∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R) ∧
      (∀ i, vec3 (0 : L) 0 (((C * V * g₀) *ᵥ b) i) ∈ R) ∧
      ∀ i, vec3 (0 : L) 0 (((g₀ * C * U) *ᵥ b) i) ∈ R := by
  obtain ⟨hU, hV, hC, hgC, e⟩ := hf
  have e' : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 e
  have h1' : ∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) ((0 : Fin N → L) k) ∈ R := h1
  have c1 : ∀ {X : Matrix (Fin N) (Fin N) L}, IsInt X → ∀ i, vec3 (0 : L) (X i) 0 ∈ R := fun {X} hX i => by
    simpa using comb R hX 1 0 h1' i
  have c2 : ∀ {X : Matrix (Fin N) (Fin N) L}, IsInt X → ∀ i,
      vec3 (0 : L) ((X * g₀) i) (((X * g₀) *ᵥ b) i) ∈ R := fun {X} hX i => by
    simpa [Matrix.mulVec_mulVec] using comb R hX g₀ (g₀ *ᵥ b) h2 i
  have eA : C * V * g₀ = 1 - C * U := by
    rw [← e', Matrix.mul_add, Matrix.mul_assoc C V g₀]
    abel
  have iA : IsInt (C * V * g₀) := fun i j => by
    rw [eA]
    exact sub_mem (isInt_one i j) ((hC.mul hU) i j)
  have eB : (1 - g₀ * C * V) * g₀ = g₀ * C * U := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc g₀ C V, Matrix.mul_assoc g₀ (C * V) g₀, eA, Matrix.mul_sub,
      Matrix.mul_one, Matrix.mul_assoc g₀ C U]
    abel
  have iB : IsInt (1 - g₀ * C * V) := fun i j => sub_mem (isInt_one i j) ((hgC.mul hV) i j)
  refine ⟨fun k => ?_, fun i => ?_, fun i => ?_⟩
  · have := R.add_mem (c1 hU k) (c2 hV k)
    rwa [vec3_add, zero_add] at this
  · have := R.sub_mem (c2 (hC.mul hV) i) (c1 iA i)
    rwa [blockVector_sub, sub_self, sub_zero] at this
  · have := R.sub_mem (c2 iB i) (c1 (hgC.mul hU) i)
    rwa [eB, blockVector_sub, sub_self, sub_zero] at this
end GlobalTheory.CompanionTheory.InertSpan
