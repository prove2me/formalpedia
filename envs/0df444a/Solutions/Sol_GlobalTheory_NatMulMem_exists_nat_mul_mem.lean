-- Prove2me | solution 1 for GlobalTheory.NatMulMem.exists_nat_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:02:59.962282+00:00
-- url     : https://prove2.me/submissions/50a53faa-af3e-4ac5-bdda-1f2e6a74c1f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulMem
open NumberField
namespace GlobalTheory.NatMulMem
theorem _root_.solution {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  obtain ⟨y, hy, hint⟩ :=
    IsAlgebraic.exists_integral_multiple (R := ℤ) (z := c)
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c))
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = ((y : ℤ) : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -((y : ℤ) : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hint.neg
end GlobalTheory.NatMulMem
