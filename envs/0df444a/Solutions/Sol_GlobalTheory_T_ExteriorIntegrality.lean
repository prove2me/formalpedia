-- Prove2me | solution 1 for GlobalTheory.T.ExteriorIntegrality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:41.421599+00:00
-- url     : https://prove2.me/submissions/95566db8-8765-4f48-ae4d-acc6853603f3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegralityStatement
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_first
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_wedgeInt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : WedgeInt := by
  first | exact @GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | exact GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt | (intros; apply GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt <;> assumption)
end _root_.GlobalTheory.T
