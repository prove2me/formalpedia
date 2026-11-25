-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KFinStab.kFinStab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:23:30.917846+00:00
-- url     : https://prove2.me/submissions/ee44c66c-9a3a-4fa9-8624-336dcaca7d89

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KsetSubset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemUJsetOfMemKset
import Theorems.Thm_UpperTheory_Reformulated_B_Gc1_kFinStab


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PI.UpqRep (UJset Kset IsKFin IsKStableOn)
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KFinStab
namespace GlobalTheory.CompanionTheory.KFinStab
theorem _root_.solution : CompanionTheory.D.DSIC.KFinStab :=
  _root_.UpperTheory.Reformulated.B.Gc1.kFinStab
end GlobalTheory.CompanionTheory.KFinStab
