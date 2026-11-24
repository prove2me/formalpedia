-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:40:11.033006+00:00
-- url     : https://prove2.me/submissions/3631a345-3715-454e-b083-b180abed5049

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
import Theorems.Thm_GlobalTheory_RegularNormal_StableDvd_isIntegrallyClosed
import Theorems.Thm_GlobalTheory_RegularNormal_stableDvd_of_spanFinrank_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by
  intro T _ _
  have hd : IsDomain T := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain T
  exact ⟨hd, (RegularNormal.stableDvd_of_spanFinrank_eq _ T rfl).isIntegrallyClosed⟩
end GlobalTheory
