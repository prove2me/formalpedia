-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICHWMap.sum_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:31.194569+00:00
-- url     : https://prove2.me/submissions/49ee77dc-aa53-44bc-8c35-f50374c1589a

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
theorem _root_.solution {x y : WithLp 2 (T × V)} (h1 : (WithLp.ofLp x).1 = (WithLp.ofLp y).1)
    (h2 : (WithLp.ofLp x).2 = (WithLp.ofLp y).2) : x = y := by
  apply (WithLp.linearEquiv 2 ℂ (T × V)).injective
  exact Prod.ext h1 h2
end GlobalTheory.CompanionTheory.DSICHWMap
