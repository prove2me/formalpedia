-- Prove2me | solution 2 for GlobalTheory.powGr.map_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:46.821007+00:00
-- url     : https://prove2.me/submissions/92076fdc-a6d8-44fb-86fd-93ba4940a5ab

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
variable {R : Type*} [CommRing R]
open GlobalTheory.powGr
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ)
variable {I M a}
namespace GlobalTheory.powGr
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (x : ↥(I ^ a • ⊤ : Submodule R M)) :
    map I a g (mk I M a x) =
      mk I N a ⟨g x, Submodule.smul_top_le_comap_smul_top (I ^ a) g x.2⟩ := rfl
end GlobalTheory.powGr
