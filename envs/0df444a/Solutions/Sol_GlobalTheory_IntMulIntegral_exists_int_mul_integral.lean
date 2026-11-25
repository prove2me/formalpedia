-- Prove2me | solution 1 for GlobalTheory.IntMulIntegral.exists_int_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:30:50.49489+00:00
-- url     : https://prove2.me/submissions/d6a149fb-8d0e-4ad5-9b44-bf58315aa3e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.IntMulIntegral
namespace GlobalTheory.IntMulIntegral
theorem _root_.solution {K : Type} [Field K] [NumberField K] (z : K) :
    ∃ M : ℤ, M ≠ 0 ∧ IsIntegral ℤ ((M : K) * z) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint
end GlobalTheory.IntMulIntegral
