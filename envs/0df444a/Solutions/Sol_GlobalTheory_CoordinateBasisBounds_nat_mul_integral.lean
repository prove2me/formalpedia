-- Prove2me | solution 1 for GlobalTheory.CoordinateBasisBounds.nat_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:55.724255+00:00
-- url     : https://prove2.me/submissions/e9ee0df1-84b2-4fff-88bb-85c6817902ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatMulIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordinateBasisBounds
open NumberField
namespace GlobalTheory.CoordinateBasisBounds
theorem _root_.solution {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ o : 𝓞 E, (m : E) * x = algebraMap (𝓞 E) E o := by
  have hx : IsAlgebraic ℤ x := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ x)
  obtain ⟨m, s, hm, h⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 E) hx
  exact ⟨m, Nat.pos_of_ne_zero hm, s, by rw [← h, nsmul_eq_mul]⟩
end GlobalTheory.CoordinateBasisBounds
