-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.commGroup_mul_mul_eq_mul_inv_mul_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:28.496859+00:00
-- url     : https://prove2.me/submissions/e17ebc33-051d-4b95-943f-f9b1da5114fe

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nI_fromCols_of_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {ι κ κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution [DecidableEq ι] (hD : DetMono) (hM : MulI) (B : Matrix ι κ ℂ) (Y : Matrix κ ι ℂ)
    (hYB : Y * B = 1) (hQ : (B * Y)ᴴ = B * Y) (C : Matrix ι κ' ℂ) :
    nI (fromCols B C) = nI B * nI ((1 - B * Y) * C) ∧ nI ((1 - B * Y) * C) ≤ nI C ∧
      (1 - B * Y) * B = 0 := by
  have hPP : B * Y * (B * Y) = B * Y := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y, hYB, Matrix.one_mul]
  have hQB : (1 - B * Y) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYB, Matrix.mul_one, sub_self]
  have hQh : (1 - B * Y)ᴴ = 1 - B * Y := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ]
  have hQQ : (1 - B * Y) * (1 - B * Y) = 1 - B * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]
  have hPh : (B * Y)ᴴ * (B * Y) = B * Y := by
    rw [hQ, hPP]
  refine ⟨?_, ?_, hQB⟩
  · have hcols : fromCols B C = (fromCols B ((1 - B * Y) * C) : Matrix ι (κ ⊕ κ') ℂ) *
        (fromBlocks (1 : Matrix κ κ ℂ) (Y * C) (0 : Matrix κ' κ ℂ) (1 : Matrix κ' κ' ℂ)) := by
      rw [Matrix.fromCols_mul_fromBlocks]
      congr 1
      · rw [Matrix.mul_one, Matrix.mul_zero, add_zero]
      · rw [Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
        abel
    have horth : Bᴴ * ((1 - B * Y) * C) = 0 := by
      rw [← Matrix.mul_assoc, ← hQh, ← Matrix.conjTranspose_mul, hQB, Matrix.conjTranspose_zero,
        Matrix.zero_mul]
    rw [hcols, (hM ι ι (κ ⊕ κ') (fromCols B ((1 - B * Y) * C))).2.1, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, Matrix.det_one, mul_one, norm_one, one_pow, mul_one, nI_fromCols_of_orth B _ horth]
  · have hX : ((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C) = Cᴴ * ((1 - B * Y) * C) := by
      rw [Matrix.conjTranspose_mul, hQh, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - B * Y), hQQ]
    have hYX : Cᴴ * C - ((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C) = (B * Y * C)ᴴ * (B * Y * C) := by
      rw [hX, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (B * Y)ᴴ, hPh,
        Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, sub_sub_cancel]
    exact hD κ' (((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C)) (Cᴴ * C)
      (Matrix.posSemidef_conjTranspose_mul_self _)
      (by rw [hYX]; exact Matrix.posSemidef_conjTranspose_mul_self _)
end GlobalTheory.CompanionTheory.Wedge
