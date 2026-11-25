-- Prove2me | solution 1 for GlobalTheory.T.QuantumDeterminantEquality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:13.958505+00:00
-- url     : https://prove2.me/submissions/7e78c9e7-4d75-4f87-a212-9d6a1abf5cf2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEqualityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_qdetEq


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
theorem _root_.solution : CompanionTheory.RgExh.Hk.QdetEq := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | exact GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.qdetEq <;> assumption)
end _root_.GlobalTheory.T
