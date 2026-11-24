-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:26.17701+00:00
-- url     : https://prove2.me/submissions/ec93f689-1848-43ba-9dce-1f150f7a918c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_gram_det_ne_zero_iff

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
theorem _root_.solution (B : Matrix ι κ ℂ) (hB : LinearIndependent ℂ Bᵀ) :
    ∃ Y : Matrix κ ι ℂ, Y * B = 1 ∧ (B * Y)ᴴ = B * Y := by
  have hu : IsUnit (Bᴴ * B).det := isUnit_iff_ne_zero.2 ((gram_det_ne_zero_iff B).2 hB)
  have hG : (Bᴴ * B)ᴴ = Bᴴ * B := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine ⟨(Bᴴ * B)⁻¹ * Bᴴ, ?_, ?_⟩
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hG, Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.Wedge
