-- Prove2me | solution 1 for Kyprianou.Ch03.indepPastFutureJoinEventExactAmbientV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:03:27.683377+00:00
-- url     : https://prove2.me/submissions/bae545ae-8445-4d1c-b8ee-cadef4af6d00

import Mathlib.Probability.ConditionalExpectation
import Theorems.Thm_Kyprianou_Ch03_indepPastFutureIndicatorCondExpSetIntegralV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m g h : MeasurableSpace Omega)
    (hmg : m ≤ g) (hgh : g ≤ m ⊔ h) (hjoin : m ⊔ h ≤ mΩ)
    (hInd : @Indep Omega g h mΩ P)
    (A : Set Omega) (hA : MeasurableSet[g] A) :
    ∃ B : Set Omega, MeasurableSet[m] B ∧ P ((A \ B) ∪ (B \ A)) = 0 := by
  let f : Omega → ℝ := A.indicator (fun _ => (1 : ℝ))
  let z : Omega → ℝ := P[f | m]
  have haJ : MeasurableSet[m ⊔ h] A := hgh _ hA
  have hfJ : StronglyMeasurable[m ⊔ h] f :=
    (measurable_const.indicator haJ).stronglyMeasurable
  have hf : Integrable f P :=
    (integrable_const (1 : ℝ)).indicator (hjoin _ haJ)
  have hz : StronglyMeasurable[m] z := stronglyMeasurable_condExp
  have hzJ : StronglyMeasurable[m ⊔ h] z := hz.mono le_sup_left
  have hzI : Integrable z P := integrable_condExp
  have heq : z =ᵐ[P] f := by
    have he : z =ᵐ[P] P[f | m ⊔ h] :=
      ae_eq_condExp_of_forall_setIntegral_eq hjoin hf
        (fun _ _ _ => hzI.integrableOn)
        (fun S hs _ =>
          @Kyprianou.Ch03.indepPastFutureIndicatorCondExpSetIntegralV1
            Omega mΩ P inferInstance m g h hmg hgh hjoin hInd A hA S hs)
        hzJ.aestronglyMeasurable
    rw [condExp_of_stronglyMeasurable hjoin hfJ hf] at he
    exact he
  let B : Set Omega := {x | (1 / 2 : ℝ) < z x}
  refine ⟨B, measurableSet_lt measurable_const hz.measurable, ?_⟩
  apply measure_mono_null (t := {x | ¬ z x = f x}) _ (ae_iff.mp heq)
  intro x hx hex
  have hb : x ∈ B ↔ x ∈ A := by
    change (1 / 2 : ℝ) < z x ↔ x ∈ A
    rw [hex]
    by_cases ha : x ∈ A
    · norm_num [f, ha]
    · norm_num [f, ha]
  rcases hx with hx | hx
  · exact hx.2 (hb.mpr hx.1)
  · exact hx.2 (hb.mp hx.1)
