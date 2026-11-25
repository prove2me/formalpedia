-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:04:11.03316+00:00
-- url     : https://prove2.me/submissions/9c3310ca-0d6f-4a9b-bf0d-8d27b85d81b1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Wedge_nF_nonneg__274c325c4b7e
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_ne_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_reindex
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_nF_quot

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
theorem _root_.solution : MulF → WedgeF := by
  intro hM K ι _ _ _ _
  exact
    { nonneg := fun κ _ _ A => nF_nonneg' A
      ne_zero := fun κ _ _ A => nF_ne_zero_iff hM A
      reindex := fun κ κ' _ _ _ _ e A => nF_reindex e A
      quot := fun κ _ _ B hB => nF_quot hM B hB }
end GlobalTheory.CompanionTheory.Wedge
