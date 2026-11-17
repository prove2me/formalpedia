-- Prove2me | solution 1 for NumberField.not_finrank_seventyOne_of_unramified_cyclic_of_classNumber_le_seven
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:04.419275+00:00
-- url     : https://prove2.me/submissions/2b43c433-582f-49d2-9ea6-8470f2ab1852

import Theorems.Thm_NumberField_finrank_dvd_classNumber_of_unramified_cyclic
import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber

set_option autoImplicit false

open IsDedekindDomain

namespace NumberField

/-- A class-number bound of seven excludes a cyclic degree-71 extension
unramified at every finite prime. Odd degree handles the infinite places. -/
theorem _root_.solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hfinite : ∀ v : HeightOneSpectrum (𝓞 K),
      (LanglandsTunnell.P2.Artin.primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥)
    (hclass : classNumber K ≤ 7) : Module.finrank K L ≠ 71 := by
  intro hdegree
  letI : IsUnramifiedAtInfinitePlaces K L :=
    IsUnramifiedAtInfinitePlaces_of_odd_finrank (by rw [hdegree]; decide)
  have hdvd := finrank_dvd_classNumber_of_unramified_cyclic K L hfinite
    (fun w => w.isUnramifiedIn L)
  rw [hdegree] at hdvd
  have hpos : 0 < classNumber K := Fintype.card_pos
  have hle := Nat.le_of_dvd hpos hdvd
  omega

end NumberField
