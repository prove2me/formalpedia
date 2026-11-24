-- Prove2me | solution 1 for GlobalTheory.length_quot_span_ne_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:51.046059+00:00
-- url     : https://prove2.me/submissions/d9d9074c-71f0-4841-b9ef-85b9f58f5255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_addVal_norm_eq_length
import Theorems.Thm_GlobalTheory_addVal_norm_ne_top_iff

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
    Module.length R (S ⧸ Ideal.span {x}) ≠ ⊤ ↔ x ∈ nonZeroDivisors S := by
  rw [← addVal_norm_eq_length, addVal_norm_ne_top_iff]
end GlobalTheory
