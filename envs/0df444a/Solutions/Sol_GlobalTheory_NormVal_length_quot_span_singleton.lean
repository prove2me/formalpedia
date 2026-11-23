-- Prove2me | solution 1 for GlobalTheory.NormVal.length_quot_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:18.228245+00:00
-- url     : https://prove2.me/submissions/3c4c9499-9852-4fcd-86cf-c885f8f3c6ab

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
open GlobalTheory.NormVal
variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
namespace GlobalTheory.NormVal
theorem _root_.solution (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a := Ring.ord_eq_addVal a
end GlobalTheory.NormVal
