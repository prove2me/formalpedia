-- Prove2me | solution 1 for GlobalTheory.IntegralMultiple.exists_int_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:49:54.068239+00:00
-- url     : https://prove2.me/submissions/91ce1420-72e6-48e5-b774-f8cab4dcb625

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoeSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultiple
open NumberField
namespace GlobalTheory.IntegralMultiple
theorem _root_.solution {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ a : 𝓞 E, (a : E) = (m : E) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y, hy, ⟨y • c, hint⟩, ?_⟩
  simp [zsmul_eq_mul]
end GlobalTheory.IntegralMultiple
