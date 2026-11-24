-- Prove2me | solution 1 for GlobalTheory.monoToPowGr_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:49.358958+00:00
-- url     : https://prove2.me/submissions/65561c70-8def-4dc8-b4e0-030fd2b73875

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
theorem _root_.solution [DecidableEq ι] (f : ι → R) (a : ℕ) (α : MonoDeg ι a)
    (x : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) :
    monoToPowGr M f a (Pi.single α x) =
      powGr.mulElem M (monoVal f α.1) (monoVal_mem_pow f α) x := by
  rw [monoToPowGr_apply, Finset.sum_eq_single α]
  · rw [Pi.single_eq_same]
  · intro β _ h
    rw [Pi.single_eq_of_ne h, map_zero]
  · simp
end GlobalTheory
