-- Prove2me | solution 1 for GlobalTheory.T.RootVectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:17.281362+00:00
-- url     : https://prove2.me/submissions/378a9526-cb83-47a9-9514-d29882cbf8f9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectorsStatement
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuRootVec_rootVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : RootVec := by
  first | exact @GlobalTheory.CompanionTheory.BmuRootVec.rootVec | exact GlobalTheory.CompanionTheory.BmuRootVec.rootVec | (intros; apply GlobalTheory.CompanionTheory.BmuRootVec.rootVec <;> assumption)
end _root_.GlobalTheory.T
