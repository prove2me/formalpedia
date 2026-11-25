-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckStdD.stdD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:50.484828+00:00
-- url     : https://prove2.me/submissions/f5a5816a-784b-4d6c-829a-a8d49868ccb9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StandardDifferential
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckStdD_dR_std
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckStdD_dR_dual
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckStdD_reH_add_imH

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckStdD
namespace GlobalTheory.CompanionTheory.ZuckStdD
theorem _root_.solution : StdD := by
  intro k r Y
  constructor
  · unfold FRep.dC
    rw [dR_std, dR_std]
    exact reH_add_imH k r Y
  · unfold FRep.dC
    rw [dR_dual, dR_dual]
    conv_rhs => rw [← reH_add_imH k r Y]
    rw [Matrix.transpose_add, Matrix.transpose_smul, neg_add, smul_neg]
end GlobalTheory.CompanionTheory.ZuckStdD
