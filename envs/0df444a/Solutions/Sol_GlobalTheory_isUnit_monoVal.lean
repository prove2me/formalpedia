-- Prove2me | solution 1 for GlobalTheory.isUnit_monoVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:35.90367+00:00
-- url     : https://prove2.me/submissions/f43206d2-2efb-48bf-a9b4-c4df7f50511a

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
theorem _root_.solution [CommMonoid R] {u : ι → R} (hu : ∀ i, IsUnit (u i)) (α : ι →₀ ℕ) :
    IsUnit (monoVal u α) :=
  IsUnit.prod_iff.mpr fun i _ => (hu i).pow _
end GlobalTheory
