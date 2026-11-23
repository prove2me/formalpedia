-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_forall_associatedPrimes_exists_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:10.273096+00:00
-- url     : https://prove2.me/submissions/e0f8e507-8be9-45f4-8e45-61f879a1af7c

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
variable {A : Type*} [CommRing A] [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution {x : M}
    (h : ∀ p ∈ associatedPrimes A M, ∃ s ∉ p, s • x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A x hx
  obtain ⟨s, hs, hsx⟩ := h p hp
  exact hs (hle (by simpa [Submodule.mem_colon_singleton] using hsx))
end GlobalTheory
