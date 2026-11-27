-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:40:44.245938+00:00
-- url     : https://prove2.me/submissions/07762aab-3b00-4dde-be01-9a3205388a3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_linearEquiv

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
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {M}
namespace GlobalTheory
theorem _root_.solution {N : Type*} [AddCommGroup N] [Module R N] (f : ι → R)
    (e : M ≃ₗ[R] N) : IsQuasiRegularSeq M f ↔ IsQuasiRegularSeq N f :=
  ⟨fun h => h.of_linearEquiv e, fun h => h.of_linearEquiv e.symm⟩
end GlobalTheory
