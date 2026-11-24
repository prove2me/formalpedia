-- Prove2me | solution 1 for GlobalTheory.exists_pos_nat_mul_eq_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:44.042797+00:00
-- url     : https://prove2.me/submissions/b95fb548-ffc2-42c8-afc4-2f79dd855cf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSmulEqTransposeMulDiagonalMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Finite ι] (f : ι → ℚ) :
    ∃ (b : ℕ) (g : ι → ℤ), 0 < b ∧ ∀ i, (g i : ℚ) = b * f i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose g hg using hb
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  refine ⟨((b : ℤ) * b).toNat, fun i => b * g i, ?_, fun i => ?_⟩
  · have := mul_self_pos.mpr hb0
    omega
  · have h1 : ((((b : ℤ) * b).toNat : ℕ) : ℤ) = b * b := Int.toNat_of_nonneg (mul_self_nonneg _)
    have h2 : ((((b : ℤ) * b).toNat : ℕ) : ℚ) = ((b : ℤ) : ℚ) * (b : ℤ) := by exact_mod_cast h1
    have h3 : (g i : ℚ) = ((b : ℤ) : ℚ) * f i := by
      have := hg i
      simpa [zsmul_eq_mul] using this
    rw [h2]
    push_cast
    rw [h3]
    ring
end GlobalTheory
