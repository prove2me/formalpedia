-- Prove2me | solution 1 for GlobalTheory.T.MatrixHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:50:12.784182+00:00
-- url     : https://prove2.me/submissions/9fe15187-a60e-4cbd-bbcd-a53d94d4a726

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixHom
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixHomStatement
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckMatHom_matHom


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
theorem _root_.solution : MatHom := by
  first | exact @GlobalTheory.CompanionTheory.ZuckMatHom.matHom | exact GlobalTheory.CompanionTheory.ZuckMatHom.matHom | (intros; apply GlobalTheory.CompanionTheory.ZuckMatHom.matHom <;> assumption)
end _root_.GlobalTheory.T
