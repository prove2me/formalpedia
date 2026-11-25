-- Prove2me | solution 1 for GlobalTheory.T.StandardDifferential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:50:18.284317+00:00
-- url     : https://prove2.me/submissions/2c122a6a-d510-42de-b657-6896679e49f3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StandardDifferential
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StandardDifferentialStatement
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckStdD_stdD


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
theorem _root_.solution : StdD := by
  first | exact @GlobalTheory.CompanionTheory.ZuckStdD.stdD | exact GlobalTheory.CompanionTheory.ZuckStdD.stdD | (intros; apply GlobalTheory.CompanionTheory.ZuckStdD.stdD <;> assumption)
end _root_.GlobalTheory.T
