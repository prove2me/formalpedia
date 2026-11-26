-- Prove2me | solution 1 for Kyprianou.Ch04.kernelL2ConvergenceAbsoluteL1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:18:30.434893+00:00
-- url     : https://prove2.me/submissions/7af0f97a-41da-415f-a5fb-8a91263fc426

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteMeasureL2ConvergenceL1
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- L2 convergence of equivalence classes on a finite measure implies real L1 convergence. -/
theorem solution
    {A : Type} [MeasurableSpace A] (mu : Measure A) [IsFiniteMeasure mu]
    (f : ℕ → A → ℝ) (g : A → ℝ)
    (hf : ∀ n, MemLp (f n) 2 mu) (hg : MemLp g 2 mu)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => ∫ a, |f n a - g a| ∂mu) atTop (𝓝 0) := by
  have hd := tendsto_iff_dist_tendsto_zero.mp hfg
  have he (n : ℕ) : eLpNorm (f n - g) 2 mu =
      ENNReal.ofReal (dist ((hf n).toLp (f n)) (hg.toLp g)) := by
    rw [Lp.dist_def, eLpNorm_congr_ae ((hf n).coeFn_toLp.sub hg.coeFn_toLp),
      ENNReal.ofReal_toReal ((hf n).sub hg).2.ne]
  have h2 : Tendsto (fun n => eLpNorm (f n - g) 2 mu) atTop (𝓝 0) := by
    simpa only [he, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hd
  have h1 := Kyprianou.Ch04.finiteMeasureL2ConvergenceL1 mu f g
    (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h2
  have hreal (n : ℕ) : (eLpNorm (f n - g) 1 mu).toReal =
      ∫ a, |f n a - g a| ∂mu := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
      ((hf n).sub hg).aestronglyMeasurable]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  simpa only [Function.comp_def, hreal, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp h1
