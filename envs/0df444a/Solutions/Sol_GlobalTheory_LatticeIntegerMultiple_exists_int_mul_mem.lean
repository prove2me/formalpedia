-- Prove2me | solution 1 for GlobalTheory.LatticeIntegerMultiple.exists_int_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:41:32.323048+00:00
-- url     : https://prove2.me/submissions/d36379fd-d7e6-4e83-814c-9991a1e16613

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsZsmulMemLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeIntegerMultiple
open NumberField
namespace GlobalTheory.LatticeIntegerMultiple
theorem _root_.solution {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ (m : ℤ) (b : RingOfIntegers E), m ≠ 0 ∧ algebraMap (RingOfIntegers E) E b = m • a := by
  have hQ : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have hZ : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hQ
  obtain ⟨m, hm, hi⟩ := hZ.exists_integral_multiple
  exact ⟨m, ⟨m • a, hi⟩, hm, rfl⟩
end GlobalTheory.LatticeIntegerMultiple
