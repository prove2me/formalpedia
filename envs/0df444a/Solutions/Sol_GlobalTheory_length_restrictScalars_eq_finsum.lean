-- Prove2me | solution 1 for GlobalTheory.length_restrictScalars_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:40.654439+00:00
-- url     : https://prove2.me/submissions/1f606380-b103-4c42-a198-0658b86ecaaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_finite_support_length_localizedModule
import Theorems.Thm_GlobalTheory_length_restrictScalars_eq_sum_of_subset

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
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace GlobalTheory
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    Module.length R X = ∑ᶠ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * Module.length R (S ⧸ n.asIdeal) := by
  have hf := finite_support_length_localizedModule h
  rw [length_restrictScalars_eq_sum_of_subset R h hf.toFinset (fun n hn => by simpa using hn),
    finsum_eq_sum_of_support_subset]
  intro n hn
  simpa using left_ne_zero_of_mul hn
end GlobalTheory
