-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.norm_det_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:56:01.076828+00:00
-- url     : https://prove2.me/submissions/c5478cff-9fae-45ff-9077-b1d4d098ad47

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
theorem _root_.solution [Fintype κ] [DecidableEq κ] (M : Matrix κ κ K) (e : Equiv.Perm κ) :
    ‖(M.submatrix e id).det‖ = ‖M.det‖ := by
  rw [det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
end GlobalTheory.CompanionTheory.Wedge
