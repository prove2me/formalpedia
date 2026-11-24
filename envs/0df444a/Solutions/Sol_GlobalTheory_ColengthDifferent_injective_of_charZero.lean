-- Prove2me | solution 1 for GlobalTheory.ColengthDifferent.injective_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:14:37.446526+00:00
-- url     : https://prove2.me/submissions/216389d4-f829-42c6-b950-d466c26e06c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ColengthDifferent
theorem _root_.solution {F : Type} [Field F] [CharZero F] (f : 𝓞 E →+* F) :
    Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [RingHom.comap_ker]
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro n hn
  have : f.comp (algebraMap ℤ (𝓞 E)) = Int.castRingHom F := RingHom.ext_int _ _
  rw [this] at hn
  simpa using hn
end GlobalTheory.ColengthDifferent
