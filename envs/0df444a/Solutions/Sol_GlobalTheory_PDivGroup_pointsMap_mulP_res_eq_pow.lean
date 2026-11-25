-- Prove2me | solution 1 for GlobalTheory.PDivGroup.pointsMap_mulP_res_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:55.163417+00:00
-- url     : https://prove2.me/submissions/9144fe83-f598-4dc6-8998-5157e736fb24

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
theorem _root_.solution (n : ℕ) (x : WithConv (G.A n →ₐ[O] B)) :
    pointsMap B (G.mulP n) (pointsMap B (G.res n) x) = x ^ p :=
  ofConv_injective <| Eq.symm <| (comp_mulBy_pts x.ofConv p).symm.trans <|
    AlgHom.ext fun a => congrArg x.ofConv (G.res_mulP n a).symm
end GlobalTheory.PDivGroup
