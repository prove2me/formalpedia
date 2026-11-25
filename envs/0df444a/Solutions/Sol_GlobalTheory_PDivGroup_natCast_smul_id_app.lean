-- Prove2me | solution 1 for GlobalTheory.PDivGroup.natCast_smul_id_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:37.02812+00:00
-- url     : https://prove2.me/submissions/456e95d0-b427-4971-8074-78d60141875d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_natCast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable {G H K : PDivGroup p O}
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (G : PDivGroup p O) (k n : ℕ) :
    Hom.app ((k : ℤ_[p]) • 𝟙 G) n = mulBy O _ k :=
  congrArg ofConv (pow_digit_natCast (G.hom_pow_self n (toConv (BialgHom.id O _))) k)
end GlobalTheory.PDivGroup
