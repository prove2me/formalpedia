-- Prove2me | solution 1 for GlobalTheory.SiegelUnip.adR_mul_dgC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:56.869953+00:00
-- url     : https://prove2.me/submissions/dbe7b504-472a-44f4-b739-5cd6d59ddb1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelUnipotentAntidiagonalCorner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open GlobalTheory GlobalTheory.SiegelUnip
open Matrix
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.SiegelUnip
theorem _root_.solution : adR n R * dgC n R = 0 := by
  simp [diagCols, fromCols_mul_fromRows]
end GlobalTheory.SiegelUnip
