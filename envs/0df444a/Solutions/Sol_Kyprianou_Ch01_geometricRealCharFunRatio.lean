-- Prove2me | solution 1 for Kyprianou.Ch01.geometricRealCharFunRatio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:38:41.731927+00:00
-- url     : https://prove2.me/submissions/b2656b8b-dae5-4748-9f72-3fcd11113f7e

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_discreteLawCharFun_asPGF
import Theorems.Thm_Kyprianou_Ch01_geometricMeasure_complexPGF
import Theorems.Thm_Kyprianou_Ch01_geometricToLogarithmicParameters
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

/-! Characteristic function of the strict geometric real-count law. -/
theorem solution
    (p : unitInterval.Elem) (hp : p ≠ 0) (hp1 : (p : ℝ) < 1)
    (xi : ℝ) :
    charFun ((ProbabilityTheory.geometricMeasure p).map
      (fun k : ℕ => (k : ℝ))) xi =
      (((p : ℝ) : ℂ) /
        (1 - (1 - (((p : ℝ) : ℂ))) *
          Complex.exp ((xi : ℂ) * Complex.I))) := by
  let z : ℂ := Complex.exp ((xi : ℂ) * Complex.I)
  obtain ⟨hq0, hq1, _⟩ :=
    Kyprianou.Ch01.geometricToLogarithmicParameters p hp hp1
  have hnormPhase : ‖z‖ = 1 := by
    simp [z, Complex.norm_exp, Complex.mul_re]
  have hnormQ : ‖1 - (((p : ℝ) : ℂ))‖ < 1 := by
    have hcast : (1 : ℂ) - (((p : ℝ) : ℂ)) =
        (((1 - (p : ℝ)) : ℝ) : ℂ) := by
      push_cast
      ring
    calc
      ‖(1 : ℂ) - (((p : ℝ) : ℂ))‖ =
          ‖(((1 - (p : ℝ)) : ℝ) : ℂ)‖ :=
        congrArg (fun z : ℂ => ‖z‖) hcast
      _ = |1 - (p : ℝ)| := Complex.norm_real _
      _ = 1 - (p : ℝ) := abs_of_nonneg (le_of_lt hq0)
      _ < 1 := hq1
  have hbound : ‖(1 - (((p : ℝ) : ℂ))) * z‖ < 1 := by
    simpa only [norm_mul, hnormPhase, mul_one] using hnormQ
  calc
    charFun ((ProbabilityTheory.geometricMeasure p).map
      (fun k : ℕ => (k : ℝ))) xi =
        ∫ k : ℕ, (Complex.exp (Complex.I * (xi : ℂ))) ^ k
          ∂ProbabilityTheory.geometricMeasure p :=
      Kyprianou.Ch01.discreteLawCharFun_asPGF _ xi
    _ = ∫ k : ℕ, z ^ k ∂ProbabilityTheory.geometricMeasure p := by
      simp [z, mul_comm]
    _ = (((p : ℝ) : ℂ) / (1 - (1 - (((p : ℝ) : ℂ))) * z)) :=
      Kyprianou.Ch01.geometricMeasure_complexPGF p hp z hbound
