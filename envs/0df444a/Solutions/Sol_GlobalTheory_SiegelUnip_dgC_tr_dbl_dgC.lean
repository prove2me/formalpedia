-- Prove2me | solution 1 for GlobalTheory.SiegelUnip.dgC_tr_dbl_dgC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:48:09.112882+00:00
-- url     : https://prove2.me/submissions/a37a5581-371d-43ad-8953-b16f7f56d73b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelUnipotentAntidiagonalCorner
import Theorems.Thm_GlobalTheory_SiegelUnip_adR_mul_dgC
import Theorems.Thm_GlobalTheory_SiegelUnip_dgC_tr_mul_dbl

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
theorem _root_.solution (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ * dgC n R = 0 := by
  rw [dgC_tr_mul_dbl, Matrix.mul_assoc, adR_mul_dgC, Matrix.mul_zero]
end GlobalTheory.SiegelUnip
