-- Prove2me | solution 2 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_levy_laplace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:20:52.00538+00:00
-- url     : https://prove2.me/submissions/9575dc10-548e-4074-b96c-7eab9a5ba9e3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (t : ℝ≥0) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * (W.W (t : ℝ) ω - (t : ℝ)))) P ∧
    (∫ ω, Real.exp (θ * (W.W (t : ℝ) ω - (t : ℝ))) ∂P) =
      Real.exp ((t : ℝ) * AvramDividend.Classical.laplaceExponent
        (-1) 1 (0 : Measure ℝ) θ) := by
  have h := LevyStochCalc.Brownian.BrownianMotion.hasLaw_eval_readable W t
  have h2 := HasLaw.comp (X := W.W (t : ℝ)) (Y := fun z : ℝ => z - (t : ℝ))
    ⟨by fun_prop, rfl⟩ h
  have e : (gaussianReal 0 t).map (fun z : ℝ => z - (t : ℝ)) = gaussianReal (-(t : ℝ)) t := by
    rw [gaussianReal_map_sub_const]; simp
  have hmap : P.map (fun ω => W.W (t : ℝ) ω - (t : ℝ)) = gaussianReal (-(t : ℝ)) t := by
    rw [← e]; exact h2.map_eq
  have hm := mgf_gaussianReal (X := fun ω => W.W (t : ℝ) ω - (t : ℝ)) (p := P) hmap θ
  rw [mgf] at hm
  refine ⟨?_, ?_⟩
  · have hi : Integrable (fun x : ℝ => Real.exp (θ * x)) (gaussianReal (-(t : ℝ)) t) :=
      integrable_exp_mul_gaussianReal θ
    rw [← hmap] at hi
    exact (integrable_map_measure (by fun_prop) h2.aemeasurable).1 hi |>.congr (by rfl)
  · rw [hm]
    congr 1
    simp [AvramDividend.Classical.laplaceExponent]
    ring
