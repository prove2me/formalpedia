-- Prove2me | solution 1 for GlobalTheory.map_monoVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:59.424068+00:00
-- url     : https://prove2.me/submissions/b4cb9086-36b4-4c3b-9fb0-c69b021ccead

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
theorem _root_.solution [CommMonoid R] {S F : Type*} [CommMonoid S] [FunLike F R S]
    [MonoidHomClass F R S] (φ : F) (f : ι → R) (α : ι →₀ ℕ) :
    φ (monoVal f α) = monoVal (fun i => φ (f i)) α := by
  simp [monoVal, Finsupp.prod, map_prod]
end GlobalTheory
