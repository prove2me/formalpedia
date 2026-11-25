-- Prove2me | solution 1 for GlobalTheory.PDivGroup.rigExtMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:01:49.158245+00:00
-- url     : https://prove2.me/submissions/c3c71be2-e260-4296-ba87-6c6cc446a94d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)
variable {G H K}
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (f : G ⟶ H) (c : H.cocycles) (w : H.omega) :
    rigExtMap f (H.rigMk (c, w)) = G.rigMk (cocyclesMap f c, omegaMap G H f w) := rfl
end GlobalTheory.PDivGroup
