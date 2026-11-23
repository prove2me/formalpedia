-- Prove2me | solution 1 for GlobalTheory.exists_sum_dual_apply_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:35.110682+00:00
-- url     : https://prove2.me/submissions/90e32b4d-f63d-4254-8c01-90fae86aeae2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Invertible A M] : ∃ s : Finset (Module.Dual A M × M), ∑ p ∈ s, p.1 p.2 = 1 := by
  obtain ⟨s, hs⟩ := ((Module.Invertible.linearEquiv A M).symm 1).exists_finset
  refine ⟨s, Eq.symm ?_⟩
  simpa [LinearEquiv.symm_apply_eq, Module.Invertible.linearEquiv] using hs
end GlobalTheory
