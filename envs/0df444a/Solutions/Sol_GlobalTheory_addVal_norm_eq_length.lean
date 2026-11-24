-- Prove2me | solution 1 for GlobalTheory.addVal_norm_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:04:51.296802+00:00
-- url     : https://prove2.me/submissions/b7b130a0-953f-4d75-8a4c-07c7a51ea37c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_addVal_det

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
    addVal R (Algebra.norm R x) = Module.length R (S ⧸ Ideal.span {x}) := by
  rw [Algebra.norm_apply, addVal_det]
  have h : LinearMap.range (Algebra.lmul R S x) = (Ideal.span {x}).restrictScalars R := by
    ext y
    simp [Ideal.mem_span_singleton', mul_comm]
  rw [(Submodule.quotEquivOfEq _ _ h).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {x})).length_eq]
end GlobalTheory
