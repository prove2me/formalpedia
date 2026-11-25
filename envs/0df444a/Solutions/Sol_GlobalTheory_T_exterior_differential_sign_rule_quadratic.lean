-- Prove2me | solution 1 for GlobalTheory.T.exterior_differential_sign_rule_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:48.122653+00:00
-- url     : https://prove2.me/submissions/367c297c-a1fb-4d45-a78f-33e38057f5b9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialSignRuleQuadratic
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialSignRuleQuadraticStatement
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeSplitCasimir_wedgeQ


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
theorem _root_.solution : StdD → (∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0) → WedgeQ := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ | exact GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ | (intros; apply GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ <;> assumption)
end _root_.GlobalTheory.T
