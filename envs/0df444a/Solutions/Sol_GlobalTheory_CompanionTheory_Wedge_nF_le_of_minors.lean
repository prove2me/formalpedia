-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.nF_le_of_minors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:05.895659+00:00
-- url     : https://prove2.me/submissions/e20b6271-848a-4e24-83fa-dcc6f8d306a1

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
theorem _root_.solution [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ s : κ → ι, ‖(A.submatrix s id).det‖ ≤ c) : nF A ≤ c :=
  Real.iSup_le h hc
end GlobalTheory.CompanionTheory.Wedge
