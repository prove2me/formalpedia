-- Prove2me | solution 1 for GlobalTheory.ordTop_vw_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:13.797897+00:00
-- url     : https://prove2.me/submissions/c30dbf1d-9017-4112-8973-4db979775f25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
namespace GlobalTheory
theorem _root_.solution : ordTop_vw V (0 : F) = ⊤ := if_pos rfl
end GlobalTheory
