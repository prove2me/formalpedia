-- Prove2me | solution 1 for GlobalTheory.SiegelUnip.adR_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:48:06.795534+00:00
-- url     : https://prove2.me/submissions/f2b149a5-77bb-4c7d-bc87-3f03ebe738c0

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
theorem _root_.solution : (adR n R)ᵀ = adC n R := by
  simp [adR, adC, transpose_fromCols]
end GlobalTheory.SiegelUnip
