-- Prove2me | solution 1 for GlobalTheory.IntSmulMemLatticeTwistedOperators.exists_int_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:55.235986+00:00
-- url     : https://prove2.me/submissions/b0f62801-67b3-4049-ac76-40aff58afa3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsNonzeroIntSmulMemOfIsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntSmulMemLatticeTwistedOperators
open NumberField
namespace GlobalTheory.IntSmulMemLatticeTwistedOperators
theorem _root_.solution {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a))
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint
end GlobalTheory.IntSmulMemLatticeTwistedOperators
