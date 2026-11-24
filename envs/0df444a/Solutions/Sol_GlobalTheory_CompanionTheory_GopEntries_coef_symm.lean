-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GopEntries.coef_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:06.166303+00:00
-- url     : https://prove2.me/submissions/e035d0f8-6a5e-4ae8-9316-27dc73d2af50

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreAnnApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GopEntries
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.GopEntries
theorem _root_.solution (c d : Fin n) (i j : NC ε) : coef c d i j = coef d c j i := by
  unfold coef
  congr 1
  · exact if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl
  · exact if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl
end GlobalTheory.CompanionTheory.GopEntries
