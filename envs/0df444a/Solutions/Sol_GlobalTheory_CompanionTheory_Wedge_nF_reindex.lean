-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.nF_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:53:14.542414+00:00
-- url     : https://prove2.me/submissions/3c54cd1e-157c-4ab4-aad8-90c9384d82ae

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
theorem _root_.solution [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (e : κ' ≃ κ) (A : Matrix ι κ K) : nF (A.submatrix id e) = nF A := by
  unfold nF
  refine (Equiv.arrowCongr e (Equiv.refl ι)).iSup_congr fun s => ?_
  have : (A.submatrix (Equiv.arrowCongr e (Equiv.refl ι) s) id).submatrix e e =
      (A.submatrix id e).submatrix s id := by
    ext a b
    simp
  rw [← this, det_submatrix_equiv_self]
end GlobalTheory.CompanionTheory.Wedge
