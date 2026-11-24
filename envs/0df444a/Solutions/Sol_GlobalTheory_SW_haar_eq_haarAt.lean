-- Prove2me | solution 1 for GlobalTheory.SW.haar_eq_haarAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:43.586805+00:00
-- url     : https://prove2.me/submissions/32f73776-92d0-4c79-be47-d58455955e39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Theorems.Thm_GlobalTheory_SW_HaarLevel_finite_support
import Theorems.Thm_GlobalTheory_SW_HaarLevel_haarAt_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → haar φ = haarAt R φ ∧ (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by
  intro K κ ι _ _ _ _ R φ hR h
  refine ⟨?_, HaarLevel.finite_support hR h⟩
  have hs : IsSB φ := ⟨R, hR, h⟩
  rw [haar, dif_pos hs, ← HaarLevel.haarAt_mul hR h hs.choose_spec.1,
    ← HaarLevel.haarAt_mul hs.choose_spec.1 hs.choose_spec.2 hR, mul_comm]
end GlobalTheory.SW
