-- Prove2me | solution 1 for GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:49.074972+00:00
-- url     : https://prove2.me/submissions/afe58284-c2f1-4e4d-89b6-4d36f4dd46b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_length_restrictScalars_eq_sum_of_subset
import Theorems.Thm_GlobalTheory_length_quotient_eq_inertiaDeg

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
theorem _root_.solution [IsLocalRing R] {X : Type*}
    [AddCommGroup X] [Module S X] (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0)
    (hover : ∀ n ∈ T, n.asIdeal.LiesOver (maximalIdeal R))
    (hfin : ∀ n ∈ T, Module.Finite R (S ⧸ n.asIdeal)) :
    Module.length R X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞) := by
  rw [length_restrictScalars_eq_sum_of_subset R h T hT]
  refine Finset.sum_congr rfl fun n hn => ?_
  haveI := hover n hn
  haveI := hfin n hn
  haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ n.asIdeal) :=
    Module.Finite.of_restrictScalars_finite R _ _
  rw [length_quotient_eq_inertiaDeg R (maximalIdeal R) n.asIdeal]
end GlobalTheory
