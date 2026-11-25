-- Prove2me | solution 1 for GlobalTheory.PDivGroup.TateOver.conv_succ_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:28:33.250865+00:00
-- url     : https://prove2.me/submissions/3679e37e-6a2f-40c3-9e2b-3c504c114b77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_PDiv_comp_mulBy_pts


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
variable {G H K : PDivGroup p O} {B B' : Type} [CommRing B] [Algebra O B] [CommRing B']
  [Algebra O B']
open GlobalTheory.PDivGroup.TateOver
namespace GlobalTheory.PDivGroup.TateOver
theorem _root_.solution (x : G.TateOver B) (n : ℕ) :
    x.conv (n + 1) ^ p = pointsMap B (G.res n) (x.conv n) :=
  ofConv_injective <| (comp_mulBy_pts (x.pt (n + 1)) p).symm.trans <| AlgHom.ext fun a =>
    (congrArg (x.pt (n + 1)) (G.mulP_res n a).symm).trans (x.pt_mulP n _)
end GlobalTheory.PDivGroup.TateOver
