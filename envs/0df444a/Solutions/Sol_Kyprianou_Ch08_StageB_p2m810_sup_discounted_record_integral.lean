-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_sup_discounted_record_integral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:23:13.862781+00:00
-- url     : https://prove2.me/submissions/9a8c02d5-59c9-448b-b7bd-787e70c2aad8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_record_survival_pointwise
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_scale_slope_nonnegative
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Verified reduction of record survival. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      derivWithin (W q) (Ici a) a ≠ 0 →
      (∫ l in Ioi x, ∫ ω, if tauPlus D.X l ω < reflectedSupExit D.X x a ω
          then discountedAt q (tauPlus D.X l ω) else 0 ∂P) = W q (a-x) / derivWithin (W q) (Ici a) a := by
  intro Ω mΩ P hP D ψ W hψ hW q x a hq ha hx hxa hn
  obtain ⟨hw, hd⟩ := p2m810_scale_slope_nonnegative Ω P D ψ W hψ hW q x a hq ha hx hxa
  let k := derivWithin (W q) (Ici a) a / W q a
  have hk : 0 < k := div_pos (lt_of_le_of_ne hd (Ne.symm hn)) hw
  calc
    _ = ∫ l in Ioi x, W q (a-x) / W q a * Real.exp (-k*(l-x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro l hl
      exact p2m810_record_survival_pointwise Ω P D ψ W hψ hW q x a hq ha hx hxa l hl
    _ = _ := by
      simp_rw [mul_sub, Real.exp_sub]
      rw [integral_const_mul, integral_div, integral_exp_mul_Ioi (neg_neg_of_pos hk)]
      have hE := Real.exp_ne_zero (-k*x)
      have hk0 := hk.ne'
      dsimp [k] at *
      field_simp [hE, hw.ne', hn]
      <;> ring
