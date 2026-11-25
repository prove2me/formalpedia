-- Prove2me | solution 1 for GlobalTheory.PDivGroup.omegaDualMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:31:05.908007+00:00
-- url     : https://prove2.me/submissions/86433f4a-b860-4f9e-aed7-5b3f3b5581f1

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
variable (G H K : PDivGroup p O)
variable [Fact p.Prime]
variable {G H K}
namespace GlobalTheory.PDivGroup
theorem _root_.solution (f : G ⟶ H) :
    omegaDualMap G H f = omegaMap H.dual G.dual (dualHom G H f) := rfl
end GlobalTheory.PDivGroup
