-- Prove2me | solution 1 for GlobalTheory.IntegerMultipleIntegral.exists_int_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:41.665381+00:00
-- url     : https://prove2.me/submissions/1aaef812-90f4-45d8-ad3d-02ed1d4327f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegerMultipleIntegral
namespace GlobalTheory.IntegerMultipleIntegral
theorem _root_.solution {K : Type} [Field K] [NumberField K] (k : K) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) K a = M • k := by
  have h1 : IsAlgebraic ℚ k := Algebra.IsAlgebraic.isAlgebraic k
  have h2 : IsAlgebraic ℤ k := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr h1
  obtain ⟨M, hM, hint⟩ := h2.exists_integral_multiple
  exact ⟨M, hM, ⟨M • k, hint⟩, rfl⟩
end GlobalTheory.IntegerMultipleIntegral
