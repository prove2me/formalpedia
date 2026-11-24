-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.nI_fromCols_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:53:15.655108+00:00
-- url     : https://prove2.me/submissions/6b67d67f-8a49-43c9-90da-dbf755d54673

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_gram_det_im

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
theorem _root_.solution (B : Matrix ι κ ℂ) (D : Matrix ι κ' ℂ) (h : Bᴴ * D = 0) :
    nI (fromCols B D) = nI B * nI D := by
  have h' : Dᴴ * B = 0 := by
    have h2 := congrArg Matrix.conjTranspose h
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h2
    exact h2
  show ((fromCols B D)ᴴ * fromCols B D).det.re = (Bᴴ * B).det.re * (Dᴴ * D).det.re
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols, h, h',
    Matrix.det_fromBlocks_zero₂₁, Complex.mul_re, gram_det_im B, gram_det_im D, mul_zero, sub_zero]
end GlobalTheory.CompanionTheory.Wedge
