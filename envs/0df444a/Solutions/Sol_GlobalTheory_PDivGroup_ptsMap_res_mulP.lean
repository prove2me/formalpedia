-- Prove2me | solution 1 for GlobalTheory.PDivGroup.ptsMap_res_mulP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:44:55.83826+00:00
-- url     : https://prove2.me/submissions/d856e49e-6903-4e5d-87c0-59332cc047e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
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
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable {B : Type} [CommRing B] [Algebra O B]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) (x : WithConv (G.A (n + 1) →ₐ[O] B)) :
    pointsMap B (G.res n) (pointsMap B (G.mulP n) x) = x ^ p :=
  ofConv_injective <| Eq.symm <| (comp_mulBy_pts x.ofConv p).symm.trans <|
    AlgHom.ext fun a => congrArg x.ofConv (G.mulP_res n a).symm
end GlobalTheory.PDivGroup
