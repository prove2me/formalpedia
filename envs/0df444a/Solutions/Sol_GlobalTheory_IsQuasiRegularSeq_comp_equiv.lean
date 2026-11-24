-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:06.479925+00:00
-- url     : https://prove2.me/submissions/0b7e303f-bd4c-4290-95d3-3bdc0246c94e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_monoVal_congr

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
open GlobalTheory.IsQuasiRegularSeq
namespace GlobalTheory.IsQuasiRegularSeq
theorem _root_.solution {κ : Type*} [Finite κ] {f : ι → R} (h : IsQuasiRegularSeq M f) (e : κ ≃ ι) :
    IsQuasiRegularSeq M (f ∘ e) := by
  intro a c hc α
  rw [e.surjective.range_comp] at hc ⊢
  have := h a (fun β => c ((MonoDeg.congr e a).symm β)) (by
    rw [← (MonoDeg.congr e a).sum_comp]
    simpa only [monoVal_congr, Equiv.symm_apply_apply] using hc) (MonoDeg.congr e a α)
  simpa using this
end GlobalTheory.IsQuasiRegularSeq
