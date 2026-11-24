-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_comp_equiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:29.254218+00:00
-- url     : https://prove2.me/submissions/a3c3b9a8-4812-4da5-b741-8c5b09c0ad96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_comp_equiv

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
theorem _root_.solution {κ : Type*} [Finite κ] (f : ι → R) (e : κ ≃ ι) :
    IsQuasiRegularSeq M (f ∘ e) ↔ IsQuasiRegularSeq M f :=
  ⟨fun h => by simpa [Function.comp_assoc] using h.comp_equiv e.symm, fun h => h.comp_equiv e⟩
end GlobalTheory
