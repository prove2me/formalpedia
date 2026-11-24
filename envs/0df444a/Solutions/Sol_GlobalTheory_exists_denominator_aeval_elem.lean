-- Prove2me | solution 1 for GlobalTheory.exists_denominator_aeval_elem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:06.973821+00:00
-- url     : https://prove2.me/submissions/17f70855-c21a-4d5b-a817-3356102f6bd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A)
    (h : ∀ x : A, ∃ p : E[X], aeval g p = x) (x : A) :
    ∃ c : O, c ≠ 0 ∧ ∃ p : O[X], aeval g p = c • x := by
  obtain ⟨q, rfl⟩ := h x
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors O) q, ?_⟩
  rw [← aeval_map_algebraMap E, hq, ← algebraMap_smul E b q, map_smul, algebraMap_smul]
end GlobalTheory
