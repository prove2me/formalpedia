-- Prove2me | solution 1 for GlobalTheory.CompactRep.isCompactOperator_rankOne_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:07.437861+00:00
-- url     : https://prove2.me/submissions/f2c2bb83-6ddd-4e11-8c34-ac462c52b043

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompactRep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.CompactRep
theorem _root_.solution (w : H) : IsCompactOperator (rankOne ℂ w w) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ w)).comp_clm (innerSL ℂ w)
end GlobalTheory.CompactRep
