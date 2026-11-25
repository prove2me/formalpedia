-- Prove2me | solution 1 for GlobalTheory.T.LeviDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:16:22.472273+00:00
-- url     : https://prove2.me/submissions/5e884cf1-87cf-4487-9af7-567142781fff

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecomposition
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecompositionStatement
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_leviQ


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
theorem _root_.solution : LeviQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselLevi.leviQ | exact GlobalTheory.CompanionTheory.BesselLevi.leviQ | (intros; apply GlobalTheory.CompanionTheory.BesselLevi.leviQ <;> assumption)
end _root_.GlobalTheory.T
