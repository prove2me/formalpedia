-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.car_imp_frel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:00:03.751268+00:00
-- url     : https://prove2.me/submissions/a5f7e1ae-37f8-4c2a-bb68-4d99fcdf30a9

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_frel_of_car

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSICFRel
theorem _root_.solution : CompanionTheory.D.DSIC.CAR → CompanionTheory.D.DSIC.FRel := frel_of_car
end GlobalTheory.CompanionTheory.DSICFRel
