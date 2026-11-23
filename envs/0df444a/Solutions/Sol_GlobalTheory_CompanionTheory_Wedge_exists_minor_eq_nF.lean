-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.exists_minor_eq_nF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:05.291276+00:00
-- url     : https://prove2.me/submissions/a8ce79fc-de00-4d18-83b6-623671b2e44c

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
theorem _root_.solution [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K)
    (h : nF A ≠ 0) : ∃ s : κ → ι, ‖(A.submatrix s id).det‖ = nF A := by
  have : Nonempty (κ → ι) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h (Real.iSup_of_isEmpty _)
  exact exists_eq_ciSup_of_finite (f := fun s : κ → ι => ‖(A.submatrix s id).det‖)
end GlobalTheory.CompanionTheory.Wedge
