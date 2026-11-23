-- Prove2me | solution 1 for GlobalTheory.localizedModule_mk_one_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:49.74048+00:00
-- url     : https://prove2.me/submissions/21c96ddc-76e3-40fa-b48e-dbe3659c7b2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution (p : Ideal A) [p.IsPrime] (x : M) :
    (LocalizedModule.mk x 1 : LocalizedModule p.primeCompl M) = 0 ↔ ∃ s ∉ p, s • x = 0 := by
  have := IsLocalizedModule.eq_zero_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M) (m := x)
  rw [LocalizedModule.mkLinearMap_apply] at this
  rw [this]
  exact ⟨fun ⟨s, hs⟩ ↦ ⟨s.1, s.2, hs⟩, fun ⟨s, hs, h⟩ ↦ ⟨⟨s, hs⟩, h⟩⟩
end GlobalTheory
