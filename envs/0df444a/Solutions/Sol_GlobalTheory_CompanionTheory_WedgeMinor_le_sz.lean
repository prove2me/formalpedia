-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeMinor.le_sz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:56:08.28248+00:00
-- url     : https://prove2.me/submissions/e236a302-b4ec-43d4-b1be-b6b3d108d559

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeMinor
namespace GlobalTheory.CompanionTheory.WedgeMinor
theorem _root_.solution {K ι κ : Type} [NormedField K] [Finite ι] [Finite κ] (g : Matrix ι κ K)
    (i : ι) (j : κ) : ‖g i j‖ ≤ sz g :=
  le_ciSup (f := fun p : ι × κ => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (i, j)
end GlobalTheory.CompanionTheory.WedgeMinor
