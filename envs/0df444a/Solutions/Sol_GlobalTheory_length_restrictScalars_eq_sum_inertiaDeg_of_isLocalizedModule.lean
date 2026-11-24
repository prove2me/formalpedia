-- Prove2me | solution 1 for GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg_of_isLocalizedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:35.425538+00:00
-- url     : https://prove2.me/submissions/fcbf2f39-7890-4a80-b286-64bc0de04e89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_length_eq_length_localizedModule
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
theorem _root_.solution [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X]
    (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)] [∀ n, Algebra S (A n)]
    [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
    (Y : MaximalSpectrum S → Type*) [∀ n, AddCommGroup (Y n)] [∀ n, Module S (Y n)]
    [∀ n, Module (A n) (Y n)] [∀ n, IsScalarTower S (A n) (Y n)]
    (f : ∀ n, X →ₗ[S] Y n) [∀ n, IsLocalizedModule n.asIdeal.primeCompl (f n)] :
    Module.length R X =
      ∑ n : MaximalSpectrum S, Module.length (A n) (Y n) * (n.asIdeal.inertiaDeg R : ℕ∞) := by
  rw [length_restrictScalars_eq_sum_inertiaDeg R S h]
  exact Finset.sum_congr rfl fun n _ => by
    rw [length_eq_length_localizedModule n.asIdeal.primeCompl (A n) (f n)]
end GlobalTheory
