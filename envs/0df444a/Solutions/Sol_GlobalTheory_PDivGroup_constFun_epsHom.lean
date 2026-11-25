-- Prove2me | solution 1 for GlobalTheory.PDivGroup.constFun_epsHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:04:26.970191+00:00
-- url     : https://prove2.me/submissions/4e604fd3-4efb-492d-80ef-e47a5b9f7e73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDiv_convPow_apply_groupLike


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
variable {G H : PDivGroup p O}
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n) (n k : ℕ) :
    constFun p O n ((epsHom ζ h0 h).app n (muT O _)) k = ζ n ^ k :=
  (constFun_constHom _ n k _).trans <|
    (convPow_apply_groupLike _ (isGroupLikeElem_muT O _) k).trans
      (congrArg (· ^ k) (muRoot_muTate ζ h0 h n))
end GlobalTheory.PDivGroup
