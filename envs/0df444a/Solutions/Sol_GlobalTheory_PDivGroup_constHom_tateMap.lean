-- Prove2me | solution 1 for GlobalTheory.PDivGroup.constHom_tateMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:42.34823+00:00
-- url     : https://prove2.me/submissions/cc7ce8a1-3ca6-4169-a858-05a3b0a6eb97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective

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
theorem _root_.solution (f : G ⟶ H) (t : G.Tate) :
    constHom H (tateMap G H O f t) = constHom G t ≫ f := by
  rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_comp, tateMap_constHom]
end GlobalTheory.PDivGroup
