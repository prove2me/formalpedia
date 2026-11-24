-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Implements.refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:33.53489+00:00
-- url     : https://prove2.me/submissions/31bef5bf-cbce-4096-844f-7bac6e4b1faa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
variable {S}
namespace GlobalTheory.CompanionTheory.FinHeis
namespace Implements
theorem _root_.solution : Implements S (AddEquiv.refl X) LinearMap.id := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
end Implements
end GlobalTheory.CompanionTheory.FinHeis
