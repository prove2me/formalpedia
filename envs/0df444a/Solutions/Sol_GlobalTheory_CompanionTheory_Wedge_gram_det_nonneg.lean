-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.gram_det_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:05.560689+00:00
-- url     : https://prove2.me/submissions/4efc2022-e4fb-4252-a5bd-81428b6c31a8

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
theorem _root_.solution (A : Matrix ι κ ℂ) : 0 ≤ (Aᴴ * A).det := by
  exact (Matrix.posSemidef_conjTranspose_mul_self A).det_nonneg
end GlobalTheory.CompanionTheory.Wedge
