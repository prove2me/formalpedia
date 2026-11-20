-- Prove2me | solution 1 for LevyStochCalc.Probability.tendsto_eLpNorm_exp_I_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:23:57.187646+00:00
-- url     : https://prove2.me/submissions/371fc7e2-7e88-48ca-8c88-818f1882ced9

import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F001

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Probability

theorem _root_.solution {α : Type*} [MeasurableSpace α] {m : Measure α} (u : ℝ)
    {Y : ℕ → α → ℝ} {Y' : α → ℝ}
    (hc : Tendsto (fun n => eLpNorm (fun x => Y n x - Y' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Complex.exp (Complex.I * ((u * Y n x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))) 2 m) atTop (𝓝 0) := by
  have pt : ∀ a b : ℝ, ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖
      ≤ ‖a - b‖ := by
    intro a b
    have e : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))
        = Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      push_cast; ring
    rw [e, norm_mul]
    have h1 : ‖Complex.exp (Complex.I * (b : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I b
    rw [h1, one_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  have hle : ∀ n, eLpNorm (fun x => Complex.exp (Complex.I * ((u * Y n x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))) 2 m
      ≤ ‖u‖ₑ * eLpNorm (fun x => Y n x - Y' x) 2 m := by
    intro n
    rw [← eLpNorm_const_smul]
    refine eLpNorm_mono fun x => ?_
    refine (pt _ _).trans (le_of_eq ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub]
  have ht : Tendsto (fun n => ‖u‖ₑ * eLpNorm (fun x => Y n x - Y' x) 2 m) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hc (Or.inr (enorm_ne_top (x := u)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun n => zero_le) hle

end LevyStochCalc.Probability
