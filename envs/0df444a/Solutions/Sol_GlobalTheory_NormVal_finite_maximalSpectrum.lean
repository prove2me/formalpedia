-- Prove2me | solution 1 for GlobalTheory.NormVal.finite_maximalSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:02:12.261814+00:00
-- url     : https://prove2.me/submissions/61ebfe1f-12d2-4c64-838a-18eca352302c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_liesOver_maximalIdeal

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
include R
namespace GlobalTheory.NormVal
theorem _root_.solution : Finite (MaximalSpectrum S) := by
  have := Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) (maximalIdeal R)
  have := this.to_subtype
  refine Finite.of_injective (fun n : MaximalSpectrum S =>
    (⟨n.asIdeal, n.isMaximal.isPrime, liesOver_maximalIdeal R n.asIdeal⟩ :
      (maximalIdeal R).primesOver S)) ?_
  intro a b h
  exact MaximalSpectrum.ext (congrArg Subtype.val h)
end GlobalTheory.NormVal
