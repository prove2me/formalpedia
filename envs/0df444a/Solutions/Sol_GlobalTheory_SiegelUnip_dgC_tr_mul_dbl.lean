-- Prove2me | solution 1 for GlobalTheory.SiegelUnip.dgC_tr_mul_dbl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:57.381731+00:00
-- url     : https://prove2.me/submissions/2ec7f955-7e57-4cf8-b07a-0164d6cea8e6

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
theorem _root_.solution (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ = J₀ * adR n R := by
  rw [dbl, dgC, diagCols, transpose_fromRows, fromCols_mul_fromBlocks, adR, mul_fromCols]
  simp
end GlobalTheory.SiegelUnip
