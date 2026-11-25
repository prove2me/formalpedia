-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.free_powGr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:08.839921+00:00
-- url     : https://prove2.me/submissions/94a959b2-f012-41d5-8951-92a8747fb133

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
namespace IsQuasiRegularSeq
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M] {f : ι → R}
    (h : IsQuasiRegularSeq M f) (a : ℕ)
    [Module.Free (R ⧸ Ideal.span (Set.range f))
      (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M))] :
    Module.Free (R ⧸ Ideal.span (Set.range f)) (powGr (Ideal.span (Set.range f)) M a) :=
  Module.Free.of_equiv (h.powGrEquiv a)
end IsQuasiRegularSeq
end GlobalTheory
