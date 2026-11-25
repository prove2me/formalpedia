-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IdxAd.sgl_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:39:44.831108+00:00
-- url     : https://prove2.me/submissions/e483d423-678e-4d29-9050-36753557ac56

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
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.IdxAd
theorem _root_.solution {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F) : sgl v x w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) x h
end GlobalTheory.CompanionTheory.IdxAd
