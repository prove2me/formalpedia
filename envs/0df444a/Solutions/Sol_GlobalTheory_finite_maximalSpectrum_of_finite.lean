-- Prove2me | solution 1 for GlobalTheory.finite_maximalSpectrum_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:43.266669+00:00
-- url     : https://prove2.me/submissions/9fed6223-4c28-4d16-86a4-714b53f08dc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R S] : Finite (MaximalSpectrum S) := by
  haveI := (Algebra.QuasiFinite.finite_primesOver (S := S) (maximalIdeal R)).to_subtype
  refine Finite.of_injective (fun n : MaximalSpectrum S =>
    (⟨n.asIdeal, n.isMaximal.isPrime, liesOver_maximalIdeal_of_isIntegral R S n.asIdeal⟩ :
      (maximalIdeal R).primesOver S)) fun a b hab => ?_
  exact MaximalSpectrum.ext (congrArg Subtype.val hab)
end GlobalTheory
