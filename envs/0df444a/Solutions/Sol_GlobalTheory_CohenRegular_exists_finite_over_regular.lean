-- Prove2me | solution 1 for GlobalTheory.CohenRegular.exists_finite_over_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:30:57.047038+00:00
-- url     : https://prove2.me/submissions/3e22f0c0-d55b-44d8-b2c8-b08a685f4483

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCoefficientFieldOfCharZero
import Theorems.Thm_GlobalTheory_CohenRegular_exists_coefficientField_of_charZero
import Theorems.Thm_GlobalTheory_CohenRegular_exists_coefficientField_of_prime
import Theorems.Thm_GlobalTheory_CohenRegular_exists_of_coefficientField
import Theorems.Thm_GlobalTheory_CohenRegular_exists_of_mixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CohenRegular
open MvPowerSeries GlobalTheory.CohenStructure
namespace GlobalTheory.CohenRegular
theorem _root_.solution :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
      [IsAdicComplete (IsLocalRing.maximalIdeal S) S],
      ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A) (i : A →+* S),
        Function.Injective i ∧ i.Finite := by
  intro S _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with h | rfl
  · by_cases hp0 : (p : S) = 0
    · obtain ⟨Λ, hF, h1⟩ := exists_coefficientField_of_prime S h hp0
      exact exists_of_coefficientField S Λ hF h1
    · exact exists_of_mixed S h
        (by rw [← residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ p) hp0
  · haveI := CharP.charP_to_charZero (ResidueField S)
    obtain ⟨Λ, hF, h1⟩ := exists_coefficientField_of_charZero S
    exact exists_of_coefficientField S Λ hF h1
end GlobalTheory.CohenRegular
