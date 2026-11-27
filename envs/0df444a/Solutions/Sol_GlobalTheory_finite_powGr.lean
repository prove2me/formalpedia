-- Prove2me | solution 1 for GlobalTheory.finite_powGr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:21.42323+00:00
-- url     : https://prove2.me/submissions/e1e385d1-b4d7-4c23-8428-886cbf70ce67

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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (f : ι → R)
    (a : ℕ) :
    Module.Finite (R ⧸ Ideal.span (Set.range f)) (powGr (Ideal.span (Set.range f)) M a) :=
  have : Module.Finite (R ⧸ Ideal.span (Set.range f))
      (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  Module.Finite.of_surjective _ (monoToPowGr_surjective M f a)
end GlobalTheory
