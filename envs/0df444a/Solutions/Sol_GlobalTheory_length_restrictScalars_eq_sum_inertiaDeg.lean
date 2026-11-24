-- Prove2me | solution 1 for GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:52.126798+00:00
-- url     : https://prove2.me/submissions/ae388c56-09f6-454a-ac1f-d73a95e50caa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_length_restrictScalars_eq_sum_inertiaDeg_of_subset

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
theorem _root_.solution [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    Module.length R X = ∑ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞) :=
  length_restrictScalars_eq_sum_inertiaDeg_of_subset R h Finset.univ (by simp)
    (fun n _ => liesOver_maximalIdeal_of_isIntegral R S n.asIdeal) (fun _ _ => inferInstance)
end GlobalTheory
