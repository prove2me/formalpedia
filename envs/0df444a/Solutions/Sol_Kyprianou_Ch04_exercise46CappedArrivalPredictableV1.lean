-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46CappedArrivalPredictableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:21:34.748548+00:00
-- url     : https://prove2.me/submissions/c6b94042-7b14-421a-b067-d264cd31b5f8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [m : MeasurableSpace Omega]
    (G : Filtration NNReal m)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A) :
    IsStronglyPredictable G.rightCont
      (fun t w => (((min (A w) (t : WithTop NNReal)).untopD 0 : NNReal) : Real)) := by
  let H : NNReal → Omega → Real := fun t w =>
    (((min (A w) (t : WithTop NNReal)).untopD 0 : NNReal) : Real)
  have hAdapt : StronglyAdapted G.rightCont H := by
    intro t
    have hc := (hA.min_const t).measurable_of_le
      (fun w => min_le_right (A w) (t : WithTop NNReal))
    exact (NNReal.continuous_coe.measurable.comp
      (Measurable.untopD 0 hc)).stronglyMeasurable
  apply avram_wave3_04_strongAdapted_leftContinuous_predictable hAdapt
  intro w t
  by_cases hw : A w = ⊤
  · have he : (fun s => H s w) = fun s : NNReal => (s : Real) := by
      funext s
      simp only [H, hw, min_eq_right le_top, WithTop.untopD_coe]
    rw [he]
    exact NNReal.continuous_coe.continuousWithinAt
  · let a : NNReal := (A w).untopD 0
    have ha : (a : WithTop NNReal) = A w :=
      WithTop.coe_untop₀_of_ne_top (by simpa using hw)
    have he : (fun s => H s w) = fun s : NNReal => ((min a s : NNReal) : Real) := by
      funext s
      change (((min (A w) (s : WithTop NNReal)).untopD 0 : NNReal) : Real) = _
      rw [← ha]
      simp only [← WithTop.coe_min, WithTop.untopD_coe]
    rw [he]
    exact (NNReal.continuous_coe.comp (continuous_const.min continuous_id)).continuousWithinAt
