-- Prove2me | solution 1 for GlobalTheory.IntegralMultiples.exists_int_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:57:02.766245+00:00
-- url     : https://prove2.me/submissions/1a769602-1559-4465-82cb-4ca53455387f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultiples
namespace GlobalTheory.IntegralMultiples
theorem _root_.solution {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ y : NumberField.RingOfIntegers E, (d : E) * c = (y : E) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
  exact ⟨y, hy0, ⟨y • c, hy c (Finset.mem_singleton_self c)⟩, (zsmul_eq_mul c y).symm⟩
end GlobalTheory.IntegralMultiples
