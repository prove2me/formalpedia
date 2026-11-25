-- Prove2me | solution 1 for GlobalTheory.HermForm.sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:46:33.524929+00:00
-- url     : https://prove2.me/submissions/77cebe44-7a18-4f16-baaa-ca7658cf7bd5

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (x : M) (f : ι → M) :
    h x (∑ i ∈ s, f i) = ∑ i ∈ s, h x (f i) := by simp
end GlobalTheory.HermForm
