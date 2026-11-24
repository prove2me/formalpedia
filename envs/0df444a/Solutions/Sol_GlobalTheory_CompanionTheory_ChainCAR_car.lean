-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainCAR.car
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:15:24.192713+00:00
-- url     : https://prove2.me/submissions/f7a315a0-7f08-4ee7-91a0-78cc594fb450

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreApply
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_ann_ann
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_cre_cre
import Theorems.Thm_GlobalTheory_CompanionTheory_ChainCAR_ann_cre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainCAR
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.ChainCAR
theorem _root_.solution : CompanionTheory.D.DSIC.CAR := fun _ _ _ _ _ i j => ⟨ann_ann i j, cre_cre i j, ann_cre i j⟩
end GlobalTheory.CompanionTheory.ChainCAR
