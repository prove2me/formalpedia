-- Prove2me | solution 1 for GlobalTheory.siegelSubDomain_and_domainOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:26.905802+00:00
-- url     : https://prove2.me/submissions/70d4ae72-c264-4741-b9a7-c4e3af4a897a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose
import Theorems.Thm_GlobalTheory_siegelH_subset_thetaDomain
import Theorems.Thm_GlobalTheory_isOpen_thetaDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution : SiegelSubDomainStatement ∧ DomainOpenStatement := by
  refine ⟨fun κ _ => siegelH_subset_thetaDomain, fun κ _ => ?_⟩
  exact isOpen_thetaDomain
end GlobalTheory
