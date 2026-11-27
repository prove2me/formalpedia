-- Prove2me | solution 1 for KStar.Choice.isDiv_complex_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:50:30.665729+00:00
-- url     : https://prove2.me/submissions/c42838b2-430e-4a69-a0eb-72e3992cb9e9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_ExtAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Choice
namespace KStar.Choice
theorem _root_.solution : IsDiv ℂˣ ∧ IsDiv Circle := by
  refine ⟨fun n hn z => ?_, fun n hn z => ?_⟩
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (Nat.pos_of_ne_zero hn)
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hw
      exact z.ne_zero hw.symm
    refine ⟨Units.mk0 w hw0, ?_⟩
    ext
    simp [hw]
  · refine ⟨Circle.exp ((z : ℂ).arg / n), ?_⟩
    simp only
    rw [← Circle.exp_natCast_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn), Circle.exp_arg]
end KStar.Choice
