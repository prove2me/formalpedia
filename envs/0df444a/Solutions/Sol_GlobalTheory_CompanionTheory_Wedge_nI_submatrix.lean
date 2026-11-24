-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.nI_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:55:48.688315+00:00
-- url     : https://prove2.me/submissions/c823e0d0-9fda-4081-a4a6-4e9123ab43e6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces

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
theorem _root_.solution (e : κ' ≃ κ) (A : Matrix ι κ ℂ) : nI (A.submatrix id e) = nI A := by
  show ((A.submatrix id e)ᴴ * A.submatrix id e).det.re = (Aᴴ * A).det.re
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul Aᴴ A (⇑e) id (⇑e) Function.bijective_id,
    Matrix.det_submatrix_equiv_self]
end GlobalTheory.CompanionTheory.Wedge
