-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.minor_le_nF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:02.831332+00:00
-- url     : https://prove2.me/submissions/fa8c0579-7613-4a93-880d-c37665f3d432

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
theorem _root_.solution [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) (s : κ → ι) :
    ‖(A.submatrix s id).det‖ ≤ nF A :=
  le_ciSup (f := fun s : κ → ι => ‖(A.submatrix s id).det‖) (Set.finite_range _).bddAbove s
end GlobalTheory.CompanionTheory.Wedge
