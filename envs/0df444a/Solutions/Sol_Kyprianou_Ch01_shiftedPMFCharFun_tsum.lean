-- Prove2me | solution 1 for Kyprianou.Ch01.shiftedPMFCharFun_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:15:50.396269+00:00
-- url     : https://prove2.me/submissions/0632e1af-ad93-420c-bf04-5b750a81f808

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

/-! The characteristic function of a shifted integer-valued PMF is its Fourier series. -/
theorem solution
    (jump : PMF ℕ) (xi : ℝ) :
    charFun (jump.toMeasure.map
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) xi =
      ∑' n : ℕ, (jump n).toReal •
        Complex.exp
          ((xi : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I) := by
  let f : ℕ → ℂ := fun n =>
    Complex.exp
      ((xi : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I)
  have hm : Measurable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
    fun_prop
  have hi : Integrable f jump.toMeasure := by
    have hf : AEStronglyMeasurable f jump.toMeasure := by
      fun_prop
    refine Integrable.of_bound hf 1 (Filter.Eventually.of_forall ?_)
    intro n
    dsimp [f]
    simp [Complex.norm_exp, Complex.mul_re]
  rw [MeasureTheory.charFun_apply_real]
  rw [MeasureTheory.integral_map hm.aemeasurable (by fun_prop)]
  exact PMF.integral_eq_tsum jump f hi
