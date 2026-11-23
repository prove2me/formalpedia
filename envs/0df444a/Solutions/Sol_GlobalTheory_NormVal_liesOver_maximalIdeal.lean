-- Prove2me | solution 1 for GlobalTheory.NormVal.liesOver_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:21.672181+00:00
-- url     : https://prove2.me/submissions/575ca09a-19de-47f1-9d19-fb55688c3d85

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
variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]
namespace GlobalTheory.NormVal
theorem _root_.solution (n : Ideal S) [n.IsMaximal] : n.LiesOver (maximalIdeal R) :=
  ⟨(eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)).symm⟩
end GlobalTheory.NormVal
