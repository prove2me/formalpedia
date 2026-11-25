-- Prove2me | solution 1 for GlobalTheory.T.HeckeBackwardStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:36:34.512121+00:00
-- url     : https://prove2.me/submissions/34c71790-8d03-40f0-bff5-2063c72af706

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeBackwardStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeBackwardStableStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgHeckeBack_backStable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : CompanionTheory.RgExh.Hk.BackStable := by
  first | exact @GlobalTheory.CompanionTheory.RgHeckeBack.backStable | exact GlobalTheory.CompanionTheory.RgHeckeBack.backStable | (intros; apply GlobalTheory.CompanionTheory.RgHeckeBack.backStable <;> assumption)
end _root_.GlobalTheory.T
