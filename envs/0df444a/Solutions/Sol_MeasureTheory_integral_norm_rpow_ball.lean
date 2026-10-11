-- Prove2me | solution 1 for MeasureTheory.integral_norm_rpow_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T16:57:20.176052+00:00
-- url     : https://prove2.me/submissions/12b7ae00-872b-4a0b-87c5-c234ee3050c0

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Metric
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ (α - n)) (ball 0 R) ∧
      (∫ z : EuclideanSpace ℝ (Fin n) in ball 0 R, ‖z‖ ^ (α - n)) =
        (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * R ^ α / α := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hp : (n - 1 : ℕ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  have heq : ∀ r : ℝ, 0 < r → r ^ (n - 1) * r ^ (α - n) = r ^ (α - 1) := by
    intro r hr
    rw [← Real.rpow_natCast, ← Real.rpow_add hr, hp]
    congr 1
    ring
  have hi : IntegrableOn (fun r : ℝ => r ^ (α - 1)) (Ioo 0 R) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hR]
    linarith
  have hiw : IntegrableOn (fun r : ℝ => r ^ (n - 1) * r ^ (α - n)) (Ioo 0 R) :=
    hi.congr_fun (fun r hr => (heq r hr.1).symm) measurableSet_Ioo
  refine ⟨?_, ?_⟩
  · exact (integrableOn_fun_norm_addHaar (E := EuclideanSpace ℝ (Fin n))
      volume (f := fun r : ℝ => r ^ (α - n))).2
        (by simpa [finrank_euclideanSpace, smul_eq_mul] using hiw)
  · have hrad := integral_fun_norm_addHaar
      (E := EuclideanSpace ℝ (Fin n)) volume ((Iio R).indicator (fun r : ℝ => r ^ (α - n)))
    have hleft : (fun z : EuclideanSpace ℝ (Fin n) =>
        (Iio R).indicator (fun r : ℝ => r ^ (α - n)) ‖z‖) =
        (ball 0 R).indicator (fun z => ‖z‖ ^ (α - n)) := by
      funext z
      simp [indicator]
    have hright : (fun r : ℝ => r ^ (n - 1) *
        (Iio R).indicator (fun r : ℝ => r ^ (α - n)) r) =
        (Iio R).indicator (fun r : ℝ => r ^ (n - 1) * r ^ (α - n)) := by
      funext r
      by_cases hr : r < R <;> simp [indicator, hr]
    simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul] at hrad
    rw [hleft, integral_indicator measurableSet_ball, hright,
      setIntegral_indicator measurableSet_Iio] at hrad
    have hset : Ioi (0 : ℝ) ∩ Iio R = Ioo 0 R := by ext r; simp
    rw [hset, setIntegral_congr_fun measurableSet_Ioo (fun r hr => heq r hr.1)] at hrad
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
      integral_rpow (Or.inl (by linarith : -1 < α - 1))] at hrad
    simpa [show α - 1 + 1 = α by ring, Real.zero_rpow hα.ne', sub_zero, mul_div_assoc,
      mul_assoc]
      using hrad
