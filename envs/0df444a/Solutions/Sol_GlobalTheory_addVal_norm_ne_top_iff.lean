-- Prove2me | solution 1 for GlobalTheory.addVal_norm_ne_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:39.214495+00:00
-- url     : https://prove2.me/submissions/46e27e91-148e-436b-b60c-7d541afbf2e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
namespace GlobalTheory
theorem _root_.solution (x : S) :
    addVal R (Algebra.norm R x) ≠ ⊤ ↔ x ∈ nonZeroDivisors S := by
  rw [Ne, addVal_eq_top_iff, Algebra.norm_apply, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot', mem_nonZeroDivisors_iff_left]
  simp
end GlobalTheory
