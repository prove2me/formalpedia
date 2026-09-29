-- Prove2me | solution 1 for Martingale.tendstoInDistribution_gaussian_of_tendsto_charFun
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:38:59.906147+00:00
-- url     : https://prove2.me/submissions/4aecffd5-d8af-4fb5-b594-24a08bb3aa9b

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (v : ℝ) (hv : 0 ≤ v)
    (h : ∀ t : ℝ, Tendsto (fun n : ℕ => ∫ ω, Complex.exp (Complex.I * t * (X n ω : ℂ)) ∂P) atTop
        (𝓝 (Complex.exp (-(v * t ^ 2) / 2)))) :
    TendstoInDistribution X atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 v.toNNReal) := by
  refine ⟨fun n => (hX n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun (fun t => ?_)
  show Tendsto (fun n : ℕ => charFun (Measure.map (X n) P) t) atTop
    (𝓝 (charFun (Measure.map id (gaussianReal 0 v.toNNReal)) t))
  -- identify the characteristic function of the law of `X n`
  have hlhs : ∀ n : ℕ, charFun (Measure.map (X n) P) t
      = ∫ ω, Complex.exp (Complex.I * t * (X n ω : ℂ)) ∂P := by
    intro n
    rw [charFun_apply_real, integral_map (hX n).aemeasurable]
    · refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      show Complex.exp ((t : ℂ) * ((X n ω : ℝ) : ℂ) * Complex.I)
          = Complex.exp (Complex.I * (t : ℂ) * ((X n ω : ℝ) : ℂ))
      congr 1
      ring
    · exact (Complex.measurable_exp.comp
        (by fun_prop : Measurable fun x : ℝ => ((t : ℂ) * (x : ℂ) * Complex.I))).aestronglyMeasurable
  -- and that of the Gaussian limit
  have hrhs : charFun (Measure.map (id : ℝ → ℝ) (gaussianReal 0 v.toNNReal)) t
      = Complex.exp (-(v * t ^ 2) / 2) := by
    rw [Measure.map_id, charFun_gaussianReal]
    congr 1
    rw [Real.coe_toNNReal v hv]
    push_cast
    ring
  rw [hrhs]
  simp only [hlhs]
  exact h t
