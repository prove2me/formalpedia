-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.CellSplit.isUnit_det_dbl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:19:37.237169+00:00
-- url     : https://prove2.me/submissions/ddf2026a-52ed-4307-8811-7a8dafc74bed

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM
namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit
theorem _root_.solution {E β : Type} [CommRing E] [Fintype β] [DecidableEq β] (J : Matrix β β E) (h : IsUnit J.det) :
    IsUnit (dbl J).det := by
  rw [show dbl J = Matrix.fromBlocks J 0 0 (-J) from rfl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
  exact h.mul ((isUnit_one.neg.pow _).mul h)
end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
