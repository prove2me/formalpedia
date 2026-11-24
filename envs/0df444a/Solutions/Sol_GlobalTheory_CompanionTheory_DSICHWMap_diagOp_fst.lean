-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICHWMap.diagOp_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:24.638378+00:00
-- url     : https://prove2.me/submissions/c8e67993-0ead-442c-b009-b61f4cea39d9

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HwMapOfLowSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICHWMap
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
variable {T V : Type} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory.CompanionTheory.DSICHWMap
theorem _root_.solution (A : Module.End ℂ T) (B : Module.End ℂ V) (x : WithLp 2 (T × V)) :
    (WithLp.ofLp (diagOp A B x)).1 = A (WithLp.ofLp x).1 := rfl
end GlobalTheory.CompanionTheory.DSICHWMap
