-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_primitive_exp_cdf_calculus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:30:19.882878+00:00
-- url     : https://prove2.me/submissions/0f66ea03-e8d2-4f8b-9c95-e2907c376d41

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_primitive_exp_product_derivative
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Weighted cumulative measure calculation. -/
theorem solution :
    ∀ (φ q : ℝ) (w f : ℝ → ℝ),
      0 < φ → 0 < q → ContinuousOn w (Ici (0 : ℝ)) →
      (∀ b : ℝ, 0 ≤ b → f b =
        q / φ * w b - q * ∫ s in (0 : ℝ)..b, w s) →
      ∀ b : ℝ, 0 ≤ b →
      Real.exp (-φ * b) * f b +
        φ * (∫ t in (0 : ℝ)..b, Real.exp (-φ * t) * f t) =
      q / φ * Real.exp (-φ * b) * w b := by
  intro φ q w f hφ hq hcont hf b hb
  let v : ℝ → ℝ := fun t => w (max t 0)
  let H : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, v s
  have hv : Continuous v :=
    hcont.comp_continuous (continuous_id.max continuous_const)
      (fun t => Set.mem_Ici.mpr (le_max_right t 0))
  have he (t : ℝ) (ht : 0 ≤ t) : H t = ∫ s in (0 : ℝ)..t, w s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    simp only [v, max_eq_left hs.1]
  have hint :
      (∫ t in (0 : ℝ)..b, Real.exp (-φ * t) * (v t - φ * H t)) =
        Real.exp (-φ*b) * H b :=
    p2m88_primitive_exp_product_derivative φ v hv b
  have hF :
      (∫ t in (0 : ℝ)..b, Real.exp (-φ * t) * f t) =
      (q / φ) * ∫ t in (0 : ℝ)..b, Real.exp (-φ * t) * (v t - φ * H t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hb] at ht
    change Real.exp (-φ * t) * f t = q / φ * (Real.exp (-φ * t) * (v t - φ * H t))
    rw [hf t ht.1, ← he t ht.1]
    simp only [v, max_eq_left ht.1]
    field_simp <;> ring
  rw [hF, hint, hf b hb, ← he b hb]
  field_simp <;> ring
