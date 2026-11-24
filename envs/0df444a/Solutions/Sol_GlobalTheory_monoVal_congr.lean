-- Prove2me | solution 1 for GlobalTheory.monoVal_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:24.366875+00:00
-- url     : https://prove2.me/submissions/4e1bf27e-bc52-4882-a02e-93c5be7a75ee

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
theorem _root_.solution [CommMonoid R] {κ : Type*} (e : ι ≃ κ) (f : κ → R) (a : ℕ)
    (α : MonoDeg ι a) : monoVal f (MonoDeg.congr e a α).1 = monoVal (f ∘ e) α.1 := by
  simp [monoVal, MonoDeg.congr, Finsupp.prod_equivMapDomain]
end GlobalTheory
