-- Prove2me | solution 1 for GlobalTheory.length_restrictScalars_local_and_semilocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:44.282929+00:00
-- url     : https://prove2.me/submissions/b7258235-96b3-4eae-acad-f9db14960688

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_length_restrictScalars_of_isLocalHom
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
namespace GlobalTheory
theorem _root_.solution (R S X : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] [AddCommGroup X] [Module R X] [Module S X]
    [IsScalarTower R S X] (h : IsFiniteLength S X) :
    (∀ [IsLocalRing S] [IsLocalHom (algebraMap R S)]
      [Module.Finite (ResidueField R) (ResidueField S)],
      Module.length R X =
        Module.length S X * (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞)) ∧
    (∀ [Module.Finite R S], Finite (MaximalSpectrum S) ∧ ∀ [Fintype (MaximalSpectrum S)],
      Module.length R X = ∑ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞)) :=
  ⟨length_restrictScalars_of_isLocalHom R S X,
    ⟨finite_maximalSpectrum_of_finite R S, length_restrictScalars_eq_sum_inertiaDeg R S h⟩⟩
end GlobalTheory
