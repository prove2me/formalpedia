-- Prove2me | solution 1 for GlobalTheory.PDivGroup.pt_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:03.661853+00:00
-- url     : https://prove2.me/submissions/bc918536-783f-48eb-995c-97343daf6167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_TateFree_exists_compat_of_surjective
import Theorems.Thm_GlobalTheory_PDivGroup_pointsMap_mulP_surjective

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
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) : Function.Surjective fun t : G.Tate => t.pt n := fun x => by
  obtain ⟨s, hs, hx⟩ := exists_compat_of_surjective n (fun k => WithConv (G.A k →ₐ[O] O))
    (fun k => pointsMap O (G.mulP k)) (G.pointsMap_mulP_surjective C) (toConv x)
  exact ⟨⟨fun k => (s k).ofConv, fun k => congrArg ofConv (hs k)⟩, congrArg ofConv hx⟩
end GlobalTheory.PDivGroup
