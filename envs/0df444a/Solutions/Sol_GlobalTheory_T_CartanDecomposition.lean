-- Prove2me | solution 1 for GlobalTheory.T.CartanDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:14:23.816388+00:00
-- url     : https://prove2.me/submissions/453f20f6-be83-4ad8-a121-6df7252c4d84

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionStatement
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_cartanQ


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
theorem _root_.solution : CartanQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselCartan.cartanQ | exact GlobalTheory.CompanionTheory.BesselCartan.cartanQ | (intros; apply GlobalTheory.CompanionTheory.BesselCartan.cartanQ <;> assumption)
end _root_.GlobalTheory.T
