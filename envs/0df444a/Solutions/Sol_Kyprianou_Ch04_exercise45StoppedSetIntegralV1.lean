-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45StoppedSetIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:38:14.654703+00:00
-- url     : https://prove2.me/submissions/1f0c29cf-cd7a-4194-9cad-5b508637d04c

import Theorems.Thm_Kyprianou_Ch04_boundedRightContinuousStopSetIntegral
import Theorems.Thm_Kyprianou_Ch04_exercise45SurvivalEventStopMeasurableV1
import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration NNReal inferInstance) (hRC : F.IsRightContinuous)
    (J : NNReal → Ω → ℝ) (hM : Martingale J F P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => J u w) (Ici t) t)
    (τ : Ω → NNReal) (ht : IsStoppingTime F (fun w => (τ w : WithTop NNReal))) :
    (∀ i, Integrable (fun w => J (min i (τ w)) w) P) ∧
    (∀ s t : NNReal, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      (∫ w in A, J (min s (τ w)) w ∂P) = ∫ w in A, J (min t (τ w)) w ∂P) := by
  letI := hRC
  have hR : F.rightCont = F := Filtration.IsRightContinuous.eq
  let V : NNReal → Ω → ℝ := fun t w => J (min t (τ w)) w
  have hstop (i : NNReal) :
      IsStoppingTime F.rightCont (fun w => (↑(min i (τ w)) : WithTop NNReal)) := by
    rw [hR]
    convert ht.min_const i using 1
    funext w
    rw [WithTop.coe_min, min_comm]
  have hsample (i : NNReal) (n : ℕ) (hi : i ≤ (n : NNReal)) :=
    Kyprianou.Ch04.boundedRightContinuousStopSetIntegral P F J
      (hR.symm ▸ hM) hr n (fun w => min i (τ w)) (hstop i)
      (fun w => (min_le_left _ _).trans hi)
  have hI (i : NNReal) : Integrable (V i) P := by
    obtain ⟨n,hn⟩ := exists_nat_gt i
    exact (hsample i n hn.le).1

  refine ⟨hI,?_⟩
  intro s t hst A hA'
  let B := A ∩ {w | s < τ w}
  have hB : MeasurableSet[F s] B := hA'.inter (by
    simpa only [Set.compl_setOf, not_le, WithTop.coe_le_coe] using (ht s).compl)
  have hBs (i : NNReal) (hi : s ≤ i) :
      MeasurableSet[(hstop i).measurableSpace] B := by
    have ht' : IsStoppingTime F.rightCont (fun w => (τ w : WithTop NNReal)) := hR.symm ▸ ht
    exact Kyprianou.Ch04.exercise45SurvivalEventStopMeasurableV1 F.rightCont τ ht'
      s i hi A (hR.symm ▸ hA') (hstop i)
  obtain ⟨n,hn⟩ := exists_nat_gt t
  have hBint : (∫ w in B, V s w ∂P) = ∫ w in B, V t w ∂P :=
    ((hsample s n (hst.trans hn.le)).2 B (hBs s le_rfl)).trans
      (((hsample t n hn.le).2 B (hBs t hst)).symm)
  have hB0 := F.le s B hB
  have hEq : EqOn (V s) (V t) (A \ B) := by
    intro w hw
    have hτ : τ w ≤ s := le_of_not_gt (fun h => hw.2 ⟨hw.1,h⟩)
    simp only [V,min_eq_right hτ,min_eq_right (hτ.trans hst)]
  have hRest := setIntegral_congr_fun ((F.le s A hA').diff hB0) hEq (μ := P)
  rw [setIntegral_sdiff hB0 (hI s).integrableOn inter_subset_left,
    setIntegral_sdiff hB0 (hI t).integrableOn inter_subset_left] at hRest
  linarith
