-- Prove2me | solution 1 for GlobalTheory.HermFrame.extForm_eq_neg_secondFormAdj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:21.740896+00:00
-- url     : https://prove2.me/submissions/677db737-b9cb-4c76-832c-b58b625328da

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_MContDiffAt_conjTranspose
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_mul
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_inv
import Theorems.Thm_GlobalTheory_HermFrame_conjTranspose_mdel
import Theorems.Thm_GlobalTheory_HermFrame_transpose_mul_conn
import Theorems.Thm_GlobalTheory_HermFrame_extForm_eq_neg_mdbar
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_HermFrame_orthLift_transpose_mul
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
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
variable {U : Set E} {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E} {k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 1 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (η : E) : extForm H z η = -secondFormAdj H z η := by
  have hz := hh.self_of_nhds
  have hs' : IsUnit (H z).toBlocks₁₁ᵀ.det := by rwa [det_transpose]

  have h1 : (H z)ᵀ * orthLift (H z) = fromRows 0 (quotGram (H z))ᵀ := by
    have := congrArg transpose (orthLift_transpose_mul hs)
    rwa [transpose_mul, transpose_transpose, transpose_fromCols, transpose_zero] at this

  have h2 : (conn H z η)ᴴ * (H z)ᵀ = (mdbar H z η)ᵀ := by
    have := congrArg conjTranspose (transpose_mul_conn hu η)
    rwa [conjTranspose_mul, hz.transpose.eq,
      show (mdel H z η)ᵀᴴ = (mdel H z η)ᴴᵀ from rfl, conjTranspose_mdel hh] at this
  have h3 : (conn H z η)ᴴ * fromRows (0 : Matrix m l ℂ) (quotGram (H z))ᵀ =
      (mdbar H z η)ᵀ * orthLift (H z) := by
    rw [← h1, ← Matrix.mul_assoc, h2]
  rw [← fromBlocks_toBlocks (conn H z η)ᴴ, ← fromBlocks_toBlocks (mdbar H z η)ᵀ, orthLift,
    fromBlocks_mul_fromRows, fromBlocks_mul_fromRows] at h3
  have h4 := congrArg toRows₁ h3
  simp only [toRows₁_fromRows, Matrix.mul_zero, zero_add, Matrix.mul_one] at h4
  have h11 : MContDiffAt 1 (fun x => (H x).toBlocks₁₁ᵀ) z := h.subGram.transpose
  have h21 : MContDiffAt 1 (fun x => (H x).toBlocks₂₁ᵀ) z :=
    (h.submatrix Sum.inr Sum.inl).transpose
  rw [extForm_eq_neg_mdbar, secondFormAdj, adj, secondForm_eq, Matrix.mul_assoc,
    show (conn H z η).toBlocks₂₁ᴴ = (conn H z η)ᴴ.toBlocks₁₂ from rfl, h4]
  simp only [orthCoeff]
  rw [mdbar_mul (h11.inv hs') h21, mdbar_inv h11 hs',
    show mdbar (fun x => (H x).toBlocks₂₁ᵀ) z η = (mdbar H z η)ᵀ.toBlocks₁₂ from rfl,
    show mdbar (fun x => (H x).toBlocks₁₁ᵀ) z η = (mdbar H z η)ᵀ.toBlocks₁₁ from rfl, subGram]
  simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel
end GlobalTheory.HermFrame
