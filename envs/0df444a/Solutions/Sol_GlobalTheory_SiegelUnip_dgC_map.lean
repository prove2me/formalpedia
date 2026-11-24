-- Prove2me | solution 1 for GlobalTheory.SiegelUnip.dgC_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:48:08.375835+00:00
-- url     : https://prove2.me/submissions/8c041ca6-1ace-4fd9-8597-04355b6606a3

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
theorem _root_.solution {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (dgC n R).map c = dgC n R := by
  rw [dgC, diagCols, fromRows_map, Matrix.map_one _ (map_zero c) (map_one c)]
end GlobalTheory.SiegelUnip
