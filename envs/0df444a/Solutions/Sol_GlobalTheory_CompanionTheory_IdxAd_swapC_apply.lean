-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IdxAd.swapC_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:39:55.475342+00:00
-- url     : https://prove2.me/submissions/964ee195-ef94-4699-8f0b-e1f679e35627

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsLatticeOfCompactOpen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SwapCApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IdxAd
namespace GlobalTheory.CompanionTheory.IdxAd
theorem _root_.solution {k : Type} [CommRing k] (z : k × k) : swapC k z = z.swap := rfl
end GlobalTheory.CompanionTheory.IdxAd
