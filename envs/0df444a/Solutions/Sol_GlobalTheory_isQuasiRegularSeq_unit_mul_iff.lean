-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_unit_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:06.609544+00:00
-- url     : https://prove2.me/submissions/4c3ed80f-4046-41d3-b91d-5c6c09ce6a53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_unit_mul
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_associated

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
theorem _root_.solution (f : ι → R) {u : ι → R} (hu : ∀ i, IsUnit (u i)) :
    (IsQuasiRegularSeq M fun i => u i * f i) ↔ IsQuasiRegularSeq M f :=
  ⟨fun h => h.of_associated fun i => associated_unit_mul_left _ _ (hu i), fun h => h.unit_mul hu⟩
end GlobalTheory
