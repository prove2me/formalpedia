-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeMinor.mulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:10.229819+00:00
-- url     : https://prove2.me/submissions/846a3c15-dd7f-4eaf-9572-9c3dbf4daa37

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_nF_mul_le
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_nF_mul_right
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_nF_square

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
theorem _root_.solution : MulF := by
  intro K ι ι' κ _ _ _ _ _ _ A
  exact ⟨fun g => nF_mul_le g A, fun s => nF_mul_right A s, fun s => nF_square s⟩
end GlobalTheory.CompanionTheory.WedgeMinor
