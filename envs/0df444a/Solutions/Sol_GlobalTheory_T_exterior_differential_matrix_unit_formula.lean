-- Prove2me | solution 1 for GlobalTheory.T.exterior_differential_matrix_unit_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:26:41.594988+00:00
-- url     : https://prove2.me/submissions/ed71b2fa-07fc-44f9-b3f0-7c7fc85c1fa0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormulaStatement
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_dC_wedge_single


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
theorem _root_.solution : ∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0 := by
  first | exact @GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single | exact GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single | (intros; apply GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single <;> assumption)
end _root_.GlobalTheory.T
