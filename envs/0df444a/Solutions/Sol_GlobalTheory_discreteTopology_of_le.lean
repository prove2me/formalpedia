-- Prove2me | solution 1 for GlobalTheory.discreteTopology_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:01.551434+00:00
-- url     : https://prove2.me/submissions/92b71556-182f-4476-8857-8e6a125a6a9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory
theorem _root_.solution {N L : Submodule ℤ V} [DiscreteTopology L] (h : N ≤ L) :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion h)
    (continuous_inclusion h) (Set.inclusion_injective h)
end GlobalTheory
