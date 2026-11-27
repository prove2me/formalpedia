-- Prove2me | solution 1 for GlobalTheory.exists_isPrimitiveRoot_of_addChar_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:27:33.557098+00:00
-- url     : https://prove2.me/submissions/283f0247-5831-43d9-99d4-8fbc4efe0ccc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsIsPrimitiveRootOfAddCharNeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R K : Type) [CommRing R] [Field K] (p : ℕ), p.Prime → (p : R) = 0 →
      ∀ ψ : AddChar R K, ψ ≠ 1 → ∃ ζ : K, IsPrimitiveRoot ζ p := by
  intro R K _ _ p hp hpR ψ hψ
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  have hpow : ψ x ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hpR, zero_mul, AddChar.map_zero_eq_one]
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (ψ x) = p := orderOf_eq_prime hpow hx
  exact ⟨ψ x, hord ▸ IsPrimitiveRoot.orderOf (ψ x)⟩
end GlobalTheory
