-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.sz_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:56:04.944299+00:00
-- url     : https://prove2.me/submissions/4ecde62b-de73-477f-94cf-c8423a58e9dc

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
theorem _root_.solution {g : Matrix ι κ K} (h : ∀ i j, ‖g i j‖ ≤ 1) : sz g ≤ 1 :=
  Real.iSup_le (fun p => h p.1 p.2) zero_le_one
end GlobalTheory.CompanionTheory.Wedge
