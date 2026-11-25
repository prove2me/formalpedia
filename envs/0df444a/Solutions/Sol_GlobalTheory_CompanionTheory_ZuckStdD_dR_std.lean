-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckStdD.dR_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:04:26.077383+00:00
-- url     : https://prove2.me/submissions/b86e9b30-551e-4503-8574-6e052cf5df41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StandardDifferential
import Theorems.Thm_PI_ComplexConjugateDerivative_exp_entry


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
theorem _root_.solution (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (vr k r false).dR X = X := by
  ext c d
  exact (PI.ComplexConjugateDerivative.exp_entry X c d).deriv
end GlobalTheory.CompanionTheory.ZuckStdD
