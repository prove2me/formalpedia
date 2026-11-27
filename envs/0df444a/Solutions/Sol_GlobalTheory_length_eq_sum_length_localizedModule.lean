-- Prove2me | solution 1 for GlobalTheory.length_eq_sum_length_localizedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:13.591789+00:00
-- url     : https://prove2.me/submissions/85993125-d5c5-48b5-92d3-7f3c470b33b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
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
    (h : IsFiniteLength S X) (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0) :
    Module.length S X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) := by
  rw [length_restrictScalars_eq_sum_of_subset S h T hT]
  refine Finset.sum_congr rfl fun n _ => ?_
  haveI : IsSimpleModule S (S ⧸ n.asIdeal) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨_, n.isMaximal, ⟨LinearEquiv.refl _ _⟩⟩
  rw [Module.length_eq_one S (S ⧸ n.asIdeal), mul_one]
end GlobalTheory
