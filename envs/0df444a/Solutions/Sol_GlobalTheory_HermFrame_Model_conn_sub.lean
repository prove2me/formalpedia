-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.conn_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:36.777856+00:00
-- url     : https://prove2.me/submissions/7484e559-6acd-4393-a1bd-a2985c1b4a1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_blockSS_eq
import Theorems.Thm_GlobalTheory_HermFrame_transpose_mul_conn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
namespace GlobalTheory.HermFrame.Model
theorem _root_.solution (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (ξ : E) :
    conn (fun x => subGram (H x)) z ξ = blockSS (H z) (conn H z ξ) := by
  have h := transpose_mul_conn hu ξ
  rw [← fromBlocks_toBlocks (H z)ᵀ, ← fromBlocks_toBlocks (conn H z ξ), fromBlocks_multiply] at h
  have h1 := congrArg toBlocks₁₁ h
  rw [toBlocks_fromBlocks₁₁] at h1
  have hs' : IsUnit (H z).toBlocks₁₁ᵀ.det := by rwa [det_transpose]
  rw [blockSS_eq, conn,
    show (mdel (fun x => subGram (H x)) z ξ)ᵀ = (mdel H z ξ)ᵀ.toBlocks₁₁ from rfl, ← h1,
    show (H z)ᵀ.toBlocks₁₁ = (H z).toBlocks₁₁ᵀ from rfl,
    show (H z)ᵀ.toBlocks₁₂ = (H z).toBlocks₂₁ᵀ from rfl, subGram, Matrix.mul_add,
    nonsing_inv_mul_cancel_left _ _ hs', orthCoeff, Matrix.mul_assoc]
end GlobalTheory.HermFrame.Model
