-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45RightContinuousStoppedMartingaleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:37:15.895875+00:00
-- url     : https://prove2.me/submissions/62670041-2ab8-4481-af38-ad8372ff6a79

import Theorems.Thm_Kyprianou_Ch04_exercise45StoppedSetIntegralV1
import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedRightContinuousStopSetIntegral
import Theorems.Thm_Kyprianou_Ch04_clippedRightContinuousAdapted
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Stopping a right-continuous martingale at a finite clock preserves its martingale property. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration NNReal inferInstance) (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (J : NNReal → Ω → ℝ) (hM : Martingale J F P)
    (hr : ∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => J u w) (Ici t) t)
    (τ : Ω → NNReal) (ht : IsStoppingTime F (fun w => (τ w : WithTop NNReal))) :
    Martingale (fun t w => J (min t (τ w)) w) F P := by
  let V : NNReal → Ω → ℝ := fun t w => J (min t (τ w)) w
  have hA : StronglyAdapted F V := by
    have h := Kyprianou.Ch04.clippedRightContinuousAdapted P F hNull J hM.stronglyAdapted hr _ ht
    have he : (fun (t : NNReal) w => J ((min (↑(τ w) : WithTop NNReal) ↑t).untopD t) w) = V := by
      funext t w
      rw [← WithTop.coe_min, WithTop.untopD_coe]
      simp only [V, min_comm]
    exact he ▸ h

  obtain ⟨hI,hEq⟩ := Kyprianou.Ch04.exercise45StoppedSetIntegralV1 P F hRC J hM hr τ ht
  refine ⟨hA,fun s t hst => ?_⟩
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hI t)
    (fun _ _ _ => (hI s).integrableOn) _ (hA s).aestronglyMeasurable
  exact fun A hA' _ => hEq s t hst A hA'
