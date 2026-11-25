-- Prove2me | solution 1 for GlobalTheory.T.PrincipalSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:14.460285+00:00
-- url     : https://prove2.me/submissions/6ae1f197-c14a-4e5e-a0be-2b37b71c0035

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSum
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSumStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_prinSum


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
theorem _root_.solution : CompanionTheory.RgExh.Hk.PrinSum := by
  first | exact @GlobalTheory.CompanionTheory.PrinSumP.prinSum | exact GlobalTheory.CompanionTheory.PrinSumP.prinSum | (intros; apply GlobalTheory.CompanionTheory.PrinSumP.prinSum <;> assumption)
end _root_.GlobalTheory.T
