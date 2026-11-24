-- Prove2me | solution 1 for GlobalTheory.monoVal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:25.759177+00:00
-- url     : https://prove2.me/submissions/9b19c716-ec6d-4917-a25c-9f22aff2ed0f

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
variable {R : Type*} {ι : Type*}
namespace GlobalTheory
theorem _root_.solution [CommMonoid R] (f g : ι → R) (α : ι →₀ ℕ) :
    monoVal (fun i => f i * g i) α = monoVal f α * monoVal g α := by
  simp [monoVal, mul_pow, Finsupp.prod_mul]
end GlobalTheory
