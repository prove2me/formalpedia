-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.gram_det_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:43.031957+00:00
-- url     : https://prove2.me/submissions/dcb25bbb-e275-4df9-8d1d-4efee10f9953

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_gram_det_nonneg

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
theorem _root_.solution (A : Matrix ι κ ℂ) : (Aᴴ * A).det.im = 0 := by
  exact (Complex.nonneg_iff.1 (gram_det_nonneg A)).2.symm
end GlobalTheory.CompanionTheory.Wedge
