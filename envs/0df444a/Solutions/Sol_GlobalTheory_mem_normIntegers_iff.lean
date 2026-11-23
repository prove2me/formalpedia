-- Prove2me | solution 1 for GlobalTheory.mem_normIntegers_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:23.791082+00:00
-- url     : https://prove2.me/submissions/53c936b2-55a6-4f30-87ea-c8ad0390e9ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C} :
    x ∈ normIntegers C ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp
end GlobalTheory
