-- Prove2me | solution 1 for GlobalTheory.powGr.map_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:25:18.193539+00:00
-- url     : https://prove2.me/submissions/6bd2c492-da33-4c8f-8e6c-14fe6522cce1

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
variable {M}
namespace GlobalTheory.powGr
theorem _root_.solution {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) : map I a (h ∘ₗ g) = map I a h ∘ₗ map I a g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := mk_surjective I M a x
  rfl
end GlobalTheory.powGr
