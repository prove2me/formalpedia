-- Prove2me | solution 1 for GlobalTheory.T.HeckeNonScalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:36:55.027585+00:00
-- url     : https://prove2.me/submissions/3f11e95d-b2c7-4bba-9173-892b60cb6b06

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalar
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalarStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_nonScal


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
theorem _root_.solution : CompanionTheory.RgExh.Hk.NonScal := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal | exact GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.nonScal <;> assumption)
end _root_.GlobalTheory.T
