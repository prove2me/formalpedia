-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_level_primitive_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:39:21.061901+00:00
-- url     : https://prove2.me/submissions/8a45ad32-11ce-40e2-8de8-717a1fc17868

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The difference of two record-level primitives is the integral
over the interval between the two record levels. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) (w : Ω)
    (a b : NNReal) (hab : a ≤ b) :
    (∫ y in Ioc (runningSup L a w) (runningSup L b w),
      Complex.exp (Complex.I * (beta:Complex) * (y:Complex)) ∂volume) =
      S L beta b w - S L beta a w := by
  let f : Real → Complex := fun y =>
    Complex.exp (Complex.I * (beta:Complex) * (y:Complex))
  have hf : Continuous f := by unfold f; fun_prop
  have ha : 0 ≤ runningSup L a w := by
    have h := (runningSup_monotone_and_path_le L w).2 (0:NNReal)
    have hm := (runningSup_monotone_and_path_le L w).1 (show (0:NNReal) ≤ a from zero_le)
    rw [L.X_zero w] at h
    exact h.trans hm
  have habU := (runningSup_monotone_and_path_le L w).1 hab
  have hb := ha.trans habU
  have h1 : IntervalIntegrable f volume (0:Real) (runningSup L a w) :=
    hf.intervalIntegrable _ _
  have h2 : IntervalIntegrable f volume (runningSup L a w) (runningSup L b w) :=
    hf.intervalIntegrable _ _
  have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
  rw [intervalIntegral.integral_of_le ha, intervalIntegral.integral_of_le habU,
    intervalIntegral.integral_of_le hb] at h
  have haeq : (∫ y in Icc (0:Real) (runningSup L a w), f y ∂volume) =
      ∫ y in Ioc (0:Real) (runningSup L a w), f y ∂volume := by
    exact integral_Icc_eq_integral_Ioc
  have hbeq : (∫ y in Icc (0:Real) (runningSup L b w), f y ∂volume) =
      ∫ y in Ioc (0:Real) (runningSup L b w), f y ∂volume := by
    exact integral_Icc_eq_integral_Ioc
  change (∫ y in Ioc (runningSup L a w) (runningSup L b w), f y ∂volume) =
    (∫ y in Icc (0:Real) (runningSup L b w), f y ∂volume) -
      (∫ y in Icc (0:Real) (runningSup L a w), f y ∂volume)
  rw [haeq,hbeq]
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h)
