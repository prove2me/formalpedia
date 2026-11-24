-- Prove2me | solution 1 for GlobalTheory.InertZeta.dual_inter_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:59:25.835711+00:00
-- url     : https://prove2.me/submissions/6c293af2-b511-480a-9cd7-9ef7e0df442f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DualInterEqSum
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_add
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_neg
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_sub
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_mulVec
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_vecMul
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_twist
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_tw_tw
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_tw_add
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_tw_neg
import Theorems.Thm_GlobalTheory_InertZeta_DualLat_tw_vecMul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_add
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_mul_inv
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
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
open GlobalTheory GlobalTheory.InertZeta
open DualLat
namespace GlobalTheory.InertZeta
theorem _root_.solution : Dual := by
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσ, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hgC, e⟩ := hF
  have e' : C * (U + V * mat g) = 1 := mul_eq_one_comm.1 e
  have hr' : r = -tw σ b := by ext j; simp [tw, hr]
  have m1 : C * V * mat g = 1 - C * U := by
    rw [Matrix.mul_assoc, ← e', Matrix.mul_add]; abel
  have m2 : C * V * mat g * mat g⁻¹ = C * V := by rw [Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
  have hCU : C * U = 1 - C * V * mat g := by rw [m1]; abel
  have m3 : mat g * C * U * mat g⁻¹ = 1 - mat g * C * V := by
    rw [Matrix.mul_assoc (mat g) C U, hCU]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, mat_mul_inv]
  change IntT t (r ᵥ* C) ↔ IntT t ((C * V * mat g) *ᵥ b) ∧ IntT t ((mat g * C * U) *ᵥ b)
  constructor
  · intro hρ
    have h1 : r = (r ᵥ* C) ᵥ* U + ((r ᵥ* C) ᵥ* V) ᵥ* mat g := by
      rw [Matrix.vecMul_vecMul (r ᵥ* C) V, ← Matrix.vecMul_add, Matrix.vecMul_vecMul, e', Matrix.vecMul_one]
    have hl₁ : IntT t (-tw σ ((r ᵥ* C) ᵥ* U)) := ((hρ.vecMul hUi).twist hσ).neg
    have hl₂ : IntT t (-tw σ ((r ᵥ* C) ᵥ* V)) := ((hρ.vecMul hVi).twist hσ).neg
    have htw : tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V)) = -r := by
      rw [tw_add, ← tw_vecMul hσσ, tw_neg, tw_neg, tw_tw hσσ, tw_tw hσσ, Matrix.neg_vecMul]
      conv_rhs => rw [h1]
      abel
    have hb : b = -tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V) := by
      calc b = tw σ (tw σ b) := (tw_tw hσσ b).symm
        _ = tw σ (tw σ (-tw σ ((r ᵥ* C) ᵥ* U) + mat g⁻¹ *ᵥ -tw σ ((r ᵥ* C) ᵥ* V))) := by
          rw [htw, hr', neg_neg]
        _ = _ := tw_tw hσσ _
    rw [hb]
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m2, m1, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (hl₁.sub (IntT.mulVec (hCi.mul hUi) hl₁)).add (IntT.mulVec (hCi.mul hVi) hl₂)
    · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, m3, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact (IntT.mulVec (hgC.mul hUi) hl₁).add (hl₂.sub (IntT.mulVec (hgC.mul hVi) hl₂))
  · rintro ⟨h1, h2⟩
    have hb : b = (C * V * mat g) *ᵥ b + (C * U) *ᵥ b := by
      rw [← Matrix.add_mulVec, m1, sub_add_cancel, Matrix.one_mulVec]
    have key : ∀ b₁ b₂ : Fin N → L,
        -tw σ (b₁ + b₂) ᵥ* C = -(tw σ b₁ ᵥ* C) - tw σ (mat g *ᵥ b₂) ᵥ* (mat g * C) := by
      intro b₁ b₂
      rw [← Matrix.vecMul_vecMul, tw_vecMul hσσ, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec, tw_add,
        Matrix.neg_vecMul, Matrix.add_vecMul]
      abel
    have h2' : IntT t (mat g *ᵥ ((C * U) *ᵥ b)) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]; exact h2
    rw [hr', hb, key]
    exact ((h1.twist hσ).vecMul hCi).neg.sub ((h2'.twist hσ).vecMul hgC)
end GlobalTheory.InertZeta
