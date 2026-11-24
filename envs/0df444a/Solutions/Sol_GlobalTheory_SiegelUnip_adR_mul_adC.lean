-- Prove2me | solution 1 for GlobalTheory.SiegelUnip.adR_mul_adC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:48:06.018026+00:00
-- url     : https://prove2.me/submissions/85bda227-4055-4a83-b051-d44a950cac80

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
theorem _root_.solution : adR n R * adC n R = 2 • (1 : Matrix (Fin n) (Fin n) R) := by
  simp [fromCols_mul_fromRows, two_smul]
end GlobalTheory.SiegelUnip
