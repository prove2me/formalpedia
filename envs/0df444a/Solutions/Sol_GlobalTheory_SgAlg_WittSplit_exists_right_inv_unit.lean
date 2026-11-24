-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.exists_right_inv_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:13.84202+00:00
-- url     : https://prove2.me/submissions/bf230e62-e12e-4a17-b7c6-93e7dc4a9b86

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_exists_left_inv_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution (φ φ' : Matrix k m F) (hφ : ∃ ψ : Matrix m k F, φ * ψ = 1)
    (hφ' : ∃ ψ : Matrix m k F, φ' * ψ = 1) : ∃ ψ : Matrix m k F, φ' * ψ = 1 ∧ IsUnit (φ * ψ).det := by
  obtain ⟨ψ1, h1⟩ := hφ
  obtain ⟨ψ2, h2⟩ := hφ'
  obtain ⟨L, hL, hLu⟩ := exists_left_inv_unit φ'ᵀ φᵀ ⟨ψ2ᵀ, by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]⟩
    ⟨ψ1ᵀ, by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]⟩
  refine ⟨Lᵀ, ?_, ?_⟩
  · rw [← Matrix.transpose_transpose φ', ← Matrix.transpose_mul, hL, Matrix.transpose_one]
  · rw [← Matrix.transpose_transpose φ, ← Matrix.transpose_mul, Matrix.det_transpose]; exact hLu
end GlobalTheory.SgAlg.WittSplit
