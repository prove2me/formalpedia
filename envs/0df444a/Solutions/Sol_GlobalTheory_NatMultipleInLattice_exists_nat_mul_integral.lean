-- Prove2me | solution 1 for GlobalTheory.NatMultipleInLattice.exists_nat_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:31.153672+00:00
-- url     : https://prove2.me/submissions/aee5aae7-7591-43a2-a592-6b239353bb49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsNsmulMemLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMultipleInLattice
namespace GlobalTheory.NatMultipleInLattice
theorem _root_.solution {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * a) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have h1 := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) * a = y • a := by
      rw [zsmul_eq_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1
  · have e : ((y.natAbs : ℕ) : E) * a = -(y • a) := by
      rw [zsmul_eq_mul, ← neg_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1.neg
end GlobalTheory.NatMultipleInLattice
