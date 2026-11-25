-- Prove2me | solution 1 for GlobalTheory.PDivGroup.muLieGen_dlogT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:30:45.627176+00:00
-- url     : https://prove2.me/submissions/27e9910b-6d2c-4f6d-aec2-13d4b5f35cc7

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
variable (p O) [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution [IsAdicComplete (Ideal.span {(p : O)}) O] :
    muLieGen p O (dlogT p O) = 1 :=
  (muOmegaEquiv p O).symm_apply_eq.2 (one_smul O _).symm
end GlobalTheory.PDivGroup
