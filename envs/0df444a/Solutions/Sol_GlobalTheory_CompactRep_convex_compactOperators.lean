-- Prove2me | solution 1 for GlobalTheory.CompactRep.convex_compactOperators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:05.666741+00:00
-- url     : https://prove2.me/submissions/5af24c7b-3c19-461d-b591-2a8023ac6356

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
theorem _root_.solution : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := by
  exact ((compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ).convex
end GlobalTheory.CompactRep
