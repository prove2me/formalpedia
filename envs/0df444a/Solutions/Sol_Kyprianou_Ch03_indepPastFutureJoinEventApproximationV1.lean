-- Prove2me | solution 1 for Kyprianou.Ch03.indepPastFutureJoinEventApproximationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:32:21.820879+00:00
-- url     : https://prove2.me/submissions/4cacdb38-5509-4560-b70b-237a02f7f808

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_indepPastFutureJoinEventExactAmbientV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

/-- Apply the ambient-measurable theorem under the completed probability measure. -/
theorem solution
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m g h : MeasurableSpace Omega)
    (hmg : m ≤ g) (hgh : g ≤ m ⊔ h)
    (hInd : @Indep Omega g h mΩ P)
    (hNull : ∀ S : Set Omega, MeasurableSet[m ⊔ h] S → @NullMeasurableSet Omega mΩ S P)
    (A : Set Omega) (hA : MeasurableSet[g] A)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ B : Set Omega, MeasurableSet[m] B ∧ P ((A \ B) ∪ (B \ A)) < ε := by
  let mc : MeasurableSpace Omega := @NullMeasurableSpace.instMeasurableSpace Omega mΩ P
  let Q : @Measure Omega mc := @Measure.completion Omega mΩ P
  have hQ (S : Set Omega) : Q S = P S := Measure.completion_apply P S
  haveI : @IsProbabilityMeasure Omega mc Q := ⟨(hQ Set.univ).trans measure_univ⟩
  have hjoin : m ⊔ h ≤ mc := fun S hS => hNull S hS
  have hi : @Indep Omega g h mc Q := by
    apply (@Indep_iff Omega g h mc Q).mpr
    intro U V hU hV
    simp only [hQ]
    exact (@Indep_iff Omega g h mΩ P).mp hInd U V hU hV
  obtain ⟨B, hB, hz⟩ :=
    @Kyprianou.Ch03.indepPastFutureJoinEventExactAmbientV1 Omega mc Q
      inferInstance m g h hmg hgh hjoin hi A hA
  exact ⟨B, hB, by rw [← hQ, hz]; exact hε⟩
