-- Prove2me | solution 1 for GlobalTheory.PDivGroup.hodgeTate_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:27.074587+00:00
-- url     : https://prove2.me/submissions/58d122c8-7c72-4dcc-b636-01a77bf38ba7

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
theorem _root_.solution (t : G.Tate) (n : ℕ) :
    (hodgeTate G t).1 n = dUnit O (toConv (t.pt n).toLinearMap : CartierDual O (G.A n)) :=
  congrArg (dUnit O) ((charHom_app_muT _ n).symm.trans (dualChar_app_muT t n))
end GlobalTheory.PDivGroup
