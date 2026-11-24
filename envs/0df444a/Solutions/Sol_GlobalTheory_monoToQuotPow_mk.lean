-- Prove2me | solution 1 for GlobalTheory.monoToQuotPow_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:50.949805+00:00
-- url     : https://prove2.me/submissions/22d90761-e59a-48a3-a58d-d31fc4a01512

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
namespace GlobalTheory
theorem _root_.solution (f : ι → R) (a : ℕ) (c : MonoDeg ι a → R) :
    monoToQuotPow f a (fun α => Ideal.Quotient.mk _ (c α)) =
      Ideal.Quotient.mk _ (∑ α, monoVal f α.1 * c α) := by
  rw [monoToQuotPow, LinearMap.sum_apply, map_sum]
  rfl
end GlobalTheory
