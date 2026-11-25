-- Prove2me | solution 1 for GlobalTheory.T.QuantumDeterminantTau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:29:19.459628+00:00
-- url     : https://prove2.me/submissions/0c7cbf7b-c5c0-4814-8aeb-0226a81fde02

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTau
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeDuality_GlRelTau
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTauStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliTwist_qdetTau


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
theorem _root_.solution : CompanionTheory.RgExh.Hk.QdetTau := by
  first | exact @GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | exact GlobalTheory.CompanionTheory.CapelliTwist.qdetTau | (intros; apply GlobalTheory.CompanionTheory.CapelliTwist.qdetTau <;> assumption)
end _root_.GlobalTheory.T
