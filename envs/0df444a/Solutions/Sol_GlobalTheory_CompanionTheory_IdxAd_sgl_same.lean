-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IdxAd.sgl_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:39:49.38179+00:00
-- url     : https://prove2.me/submissions/9e396bea-13ae-4273-bc8f-e1efe7275694

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : sgl v x v = x := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x
end GlobalTheory.CompanionTheory.IdxAd
