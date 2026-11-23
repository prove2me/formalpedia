-- Prove2me | solution 1 for GlobalTheory.weightedHomogeneousComponent_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:17.228853+00:00
-- url     : https://prove2.me/submissions/111bacf7-c4bd-446c-a159-d5dd6172b990

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
namespace GlobalTheory
theorem _root_.solution {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (n : ℤ) {p : MvPolynomial ι k}
    (hp : p ∈ I) : weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) n p ∈ I := by
  classical
  rw [← sum_homogeneousComponent p, map_sum]
  refine I.sum_mem fun i _ => ?_
  have h1 : homogeneousComponent i p ∈ weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ))
      (i : ℤ) := by
    rw [weightedHomogeneousSubmodule_one_natCast]
    exact homogeneousComponent_mem i p
  rw [weightedHomogeneousComponent_of_mem h1]
  split_ifs
  · have := hI i hp
    rwa [show (decompose (homogeneousSubmodule ι k) p i : MvPolynomial ι k) =
      homogeneousComponent i p from decomposition.decompose'_apply p i] at this
  · exact I.zero_mem
end GlobalTheory
