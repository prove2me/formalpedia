-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.conn_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:31.184125+00:00
-- url     : https://prove2.me/submissions/9dff0248-ce7e-4333-b688-484e8d48a10c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_blockQQ_eq
import Theorems.Thm_GlobalTheory_HermFrame_isUnit_det_quotGram
import Theorems.Thm_GlobalTheory_HermFrame_mdel_add
import Theorems.Thm_GlobalTheory_HermFrame_mdel_inv
import Theorems.Thm_GlobalTheory_HermFrame_mdel_mul
import Theorems.Thm_GlobalTheory_HermFrame_mdel_neg
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
namespace GlobalTheory.HermFrame.Model
theorem _root_.solution (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ : E) :
    conn (fun x => quotGram (H x)) z ξ = blockQQ (H z) (conn H z ξ) := by
  refine (eq_conn_of_compatible (H := fun x => quotGram (H x))
    (isUnit_det_quotGram hu hs) ?_).symm
  have hA : MContDiffAt 1 (fun x => (H x).toBlocks₁₁) z := h.subGram
  have hB : MContDiffAt 1 (fun x => (H x).toBlocks₁₂) z := h.submatrix Sum.inl Sum.inr
  have hC : MContDiffAt 1 (fun x => (H x).toBlocks₂₁) z := h.submatrix Sum.inr Sum.inl
  have hD : MContDiffAt 1 (fun x => (H x).toBlocks₂₂) z := h.submatrix Sum.inr Sum.inr
  have hs' : IsUnit (H z).toBlocks₁₁.det := hs
  have e := conn_transpose_mul hu ξ
  rw [← fromBlocks_toBlocks (conn H z ξ)ᵀ, ← fromBlocks_toBlocks (H z), fromBlocks_multiply] at e
  have e11 := congrArg toBlocks₁₁ e
  have e12 := congrArg toBlocks₁₂ e
  have e21 := congrArg toBlocks₂₁ e
  have e22 := congrArg toBlocks₂₂ e
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂] at e11 e12 e21 e22
  simp only [quotGram, sub_eq_add_neg]
  rw [mdel_add hD ((hC.mul (hA.inv hs')).mul hB).neg, mdel_neg, mdel_mul (hC.mul (hA.inv hs')) hB,
    mdel_mul hC (hA.inv hs'), mdel_inv hA hs',
    show mdel (fun x => (H x).toBlocks₁₁) z ξ = (mdel H z ξ).toBlocks₁₁ from rfl,
    show mdel (fun x => (H x).toBlocks₁₂) z ξ = (mdel H z ξ).toBlocks₁₂ from rfl,
    show mdel (fun x => (H x).toBlocks₂₁) z ξ = (mdel H z ξ).toBlocks₂₁ from rfl,
    show mdel (fun x => (H x).toBlocks₂₂) z ξ = (mdel H z ξ).toBlocks₂₂ from rfl,
    ← e11, ← e12, ← e21, ← e22, blockQQ_eq, transpose_sub, transpose_mul, orthCoeff, transpose_mul,
    transpose_transpose, transpose_nonsing_inv, transpose_transpose,
    show (conn H z ξ).toBlocks₂₂ᵀ = (conn H z ξ)ᵀ.toBlocks₂₂ from rfl,
    show (conn H z ξ).toBlocks₂₁ᵀ = (conn H z ξ)ᵀ.toBlocks₁₂ from rfl]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hs']
  abel
end GlobalTheory.HermFrame.Model
