-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RegenerativeCountTransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:19:14.983309+00:00
-- url     : https://prove2.me/submissions/cfa4679c-d839-4aba-8217-668f17d5462e

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (D : Set Omega) (hD : MeasurableSet D)
    (Y Z : Omega → E) (hY : Measurable Y)
    (hZ : AEMeasurable Z (P.restrict D))
    (C : E → ENNReal) (hC : Measurable C)
    (hLaw : (P.restrict D).map Z = P D • P.map Y)
    (hSplit : ∀ᵐ w ∂P, (w ∈ D → C (Y w) = 1 + C (Z w)) ∧
      (w ∉ D → C (Y w) = 1)) :
    ∀ k : Nat,
      (P {w | ((k+1+1 : Nat) : ENNReal) ≤ C (Y w)}).toReal =
        (P D).toReal * (P {w | ((k+1 : Nat) : ENNReal) ≤ C (Y w)}).toReal := by
  intro k
  let A : Set E := {x | ((k+1 : Nat) : ENNReal) ≤ C x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hC
  have he : {w | ((k+1+1 : Nat) : ENNReal) ≤ C (Y w)} =ᵐ[P]
      ((Z ⁻¹' A : Set Omega) ∩ D : Set Omega) := by
    filter_upwards [hSplit] with w hw
    apply propext
    change ((k+1+1 : Nat) : ENNReal) ≤ C (Y w) ↔
      ((k+1 : Nat) : ENNReal) ≤ C (Z w) ∧ w ∈ D
    by_cases hd : w ∈ D
    · rw [hw.1 hd, Nat.cast_add, Nat.cast_one, add_comm 1,
        ENNReal.add_le_add_iff_right ENNReal.one_ne_top]
      simp [hd]
    · rw [hw.2 hd]
      simp only [hd, and_false, iff_false]
      exact not_le.mpr (by exact_mod_cast (show 1 < k+1+1 by omega))
  rw [measure_congr he, ← Measure.restrict_apply₀' hD.nullMeasurableSet,
    ← Measure.map_apply_of_aemeasurable hZ hA, hLaw, Measure.smul_apply,
    Measure.map_apply hY hA, smul_eq_mul, ENNReal.toReal_mul]
  rfl
