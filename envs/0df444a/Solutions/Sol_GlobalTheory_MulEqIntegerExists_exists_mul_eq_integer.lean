-- Prove2me | solution 1 for GlobalTheory.MulEqIntegerExists.exists_mul_eq_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:25:41.858632+00:00
-- url     : https://prove2.me/submissions/d04ddcd6-025e-447c-af33-eb1b76e1852b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MulEqIntegerExists
open NumberField
namespace GlobalTheory.MulEqIntegerExists
theorem _root_.solution {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ a b : RingOfIntegers E, b ≠ 0 ∧ (algebraMap (RingOfIntegers E) E b) * c
      = algebraMap (RingOfIntegers E) E a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨a, b, hb0, ?_⟩
  have : algebraMap (RingOfIntegers E) E b ≠ 0 :=
    fun h => hb0 (IsFractionRing.injective (RingOfIntegers E) E (by rw [h, map_zero]))
  rw [mul_div_assoc', mul_div_cancel_left₀ _ this]
end GlobalTheory.MulEqIntegerExists
