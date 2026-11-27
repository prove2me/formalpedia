-- Prove2me | solution 1 for GlobalTheory.isFiniteLength_restrictScalars_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:05.537505+00:00
-- url     : https://prove2.me/submissions/4b400917-c5bc-467e-8b21-0a41cc98de76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_length_localizedModule_atPrime_le
import Theorems.Thm_GlobalTheory_finite_maximalSpectrum_of_finite
import Theorems.Thm_GlobalTheory_length_restrictScalars_eq_sum_inertiaDeg

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
theorem _root_.solution [Module.Finite R S] {X : Type*} [AddCommGroup X]
    [Module S X] (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    IsFiniteLength R X := by
  haveI := finite_maximalSpectrum_of_finite R S
  letI := Fintype.ofFinite (MaximalSpectrum S)
  rw [← Module.length_ne_top_iff, length_restrictScalars_eq_sum_inertiaDeg R S h]
  refine WithTop.sum_ne_top.mpr fun n _ => WithTop.mul_ne_top ?_ (ENat.coe_ne_top _)
  exact ne_top_of_le_ne_top (Module.length_ne_top_iff.mpr h)
    (length_localizedModule_atPrime_le n.asIdeal h)
end GlobalTheory
