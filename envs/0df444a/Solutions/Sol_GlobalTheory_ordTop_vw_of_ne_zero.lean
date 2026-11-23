-- Prove2me | solution 1 for GlobalTheory.ordTop_vw_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:36.122368+00:00
-- url     : https://prove2.me/submissions/2cc8d0f6-c703-46e9-9acc-40a81d2cf0af

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
theorem _root_.solution {f : F} (hf : f ≠ 0) :
    ordTop_vw V f = (WithZero.log (Ring.ordFrac V f) : ℤ) := if_neg hf
end GlobalTheory
