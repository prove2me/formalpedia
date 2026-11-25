-- Prove2me | solution 1 for GlobalTheory.T.UnitaryIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:54.293063+00:00
-- url     : https://prove2.me/submissions/13c8fa6b-5156-4f32-894c-c799826e082c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIso
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIsoStatement
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckUIso_uIso


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
theorem _root_.solution : UIso := by
  first | exact @GlobalTheory.CompanionTheory.ZuckUIso.uIso | exact GlobalTheory.CompanionTheory.ZuckUIso.uIso | (intros; apply GlobalTheory.CompanionTheory.ZuckUIso.uIso <;> assumption)
end _root_.GlobalTheory.T
