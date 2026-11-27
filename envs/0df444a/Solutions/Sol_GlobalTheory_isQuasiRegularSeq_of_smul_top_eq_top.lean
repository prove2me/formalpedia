-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_of_smul_top_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:02.369549+00:00
-- url     : https://prove2.me/submissions/31a4bf83-8682-49f5-a2f9-13c2d716bf19

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
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {M}
namespace GlobalTheory
theorem _root_.solution {f : ι → R}
    (h : (Ideal.span (Set.range f) • ⊤ : Submodule R M) = ⊤) : IsQuasiRegularSeq M f :=
  fun _ _ _ _ => by rw [h]; trivial
end GlobalTheory
