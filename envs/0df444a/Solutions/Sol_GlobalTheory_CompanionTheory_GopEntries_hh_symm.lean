-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GopEntries.hh_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:09.619452+00:00
-- url     : https://prove2.me/submissions/a2ad1418-5420-4e61-bceb-bc4c7bbd8ae4

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
theorem _root_.solution (i j : NC ε) (A B : Finset (NC ε)) : hh i j A B = hh j i B A := by
  unfold hh
  by_cases h : i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, mul_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩)]
end GlobalTheory.CompanionTheory.GopEntries
