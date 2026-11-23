-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.sel_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:46.941888+00:00
-- url     : https://prove2.me/submissions/790141a5-b9c2-4443-aa46-58dd09452846

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]
namespace GlobalTheory.CompanionTheory.Wedge
theorem _root_.solution [DecidableEq ι] [Fintype ι] (s : κ → ι) (M : Matrix ι ι' K) :
    (1 : Matrix ι ι K).submatrix s id * M = M.submatrix s id := by
  ext a b
  simp [mul_apply, one_apply]
end GlobalTheory.CompanionTheory.Wedge
