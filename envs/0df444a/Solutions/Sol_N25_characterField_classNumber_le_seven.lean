-- Prove2me | solution 1 for N25.characterField_classNumber_le_seven
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:03.198106+00:00
-- url     : https://prove2.me/submissions/b462ac31-1d2c-4546-8e2e-a4a921689bf7

import Mathlib
import Theorems.Thm_N25_characterField_exists_norm_cover
import Definitions.Def_N25_CharacterField
import Mathlib.NumberTheory.NumberField.Norm
import Theorems.Thm_N25_characterField_degree_and_totallyReal
import Definitions.Def_N25
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic
import Theorems.Thm_N25_characterField_discr_bound
import Theorems.Thm_NumberField_classNumber_le_seven_of_quintic_norm_cover

set_option autoImplicit false

noncomputable section

namespace N25

/-- The explicit H25-fixed cyclotomic field has class number at most seven. -/
theorem _root_.solution :
    NumberField.classNumber characterField ≤ 7 := by
  obtain ⟨s, hs, hcover⟩ := characterField_exists_norm_cover
  letI : NumberField.IsTotallyReal characterField := characterField_degree_and_totallyReal.2.2
  have hdreal : |(NumberField.discr characterField : ℝ)| ≤ 5 ^ 8 := by
    have hcast : ((NumberField.discr characterField).natAbs : ℝ) ≤ (5 : ℝ) ^ 8 := by
      exact_mod_cast characterField_discr_bound
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
  exact NumberField.classNumber_le_seven_of_quintic_norm_cover characterField
    characterField_degree_and_totallyReal.1
    (NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (K := characterField))
    hdreal s hs hcover

end N25
