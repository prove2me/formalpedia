-- Prove2me | solution 1 for GlobalTheory.FiniteCover.finrank_le_of_range_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:08:04.867665+00:00
-- url     : https://prove2.me/submissions/46aa7d18-5bfc-4f96-ba4c-821db8804c66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.FiniteCover
namespace GlobalTheory.FiniteCover
theorem _root_.solution {K P Q E : Type*} [Field K] [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E] [Module.Finite K Q]
    (L : P →ₗ[K] E) (hL : Function.Injective L) (B : Q →ₗ[K] E) (h : ∀ p, ∃ q, B q = L p) :
    finrank K P ≤ finrank K Q := by
  rw [← LinearMap.finrank_range_of_inj hL]
  refine (Submodule.finrank_mono (t := LinearMap.range B) ?_).trans B.finrank_range_le
  rintro _ ⟨p, rfl⟩
  exact h p
end GlobalTheory.FiniteCover
