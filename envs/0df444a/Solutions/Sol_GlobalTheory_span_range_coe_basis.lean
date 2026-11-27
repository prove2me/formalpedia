-- Prove2me | solution 1 for GlobalTheory.span_range_coe_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:05.574616+00:00
-- url     : https://prove2.me/submissions/19d1fa45-c265-4381-9a3d-f0283012f619

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
variable [FiniteDimensional ℝ V]
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} {L : Submodule ℤ V} (b : Basis ι ℤ L) :
    span ℤ (Set.range fun i => (b i : V)) = L := by
  have := congrArg (Submodule.map L.subtype) b.span_eq
  rwa [Submodule.map_span, ← Set.range_comp, map_subtype_top] at this
end GlobalTheory
