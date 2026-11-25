-- Prove2me | solution 1 for GlobalTheory.HermForm.sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:46:29.112341+00:00
-- url     : https://prove2.me/submissions/9ad2d8f6-4f7f-42c0-9959-1ea82b818eb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
open GlobalTheory.HermForm
variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable (h : HermForm R M)
namespace GlobalTheory.HermForm
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → M) (y : M) :
    h (∑ i ∈ s, f i) y = ∑ i ∈ s, h (f i) y := by simp [LinearMap.sum_apply]
end GlobalTheory.HermForm
