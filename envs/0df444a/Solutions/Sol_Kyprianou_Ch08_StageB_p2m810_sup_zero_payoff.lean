-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_sup_zero_payoff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:13:24.805438+00:00
-- url     : https://prove2.me/submissions/d6b680ca-776d-4492-a912-5acb3cc6097a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_source_tilt_derivative
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_sup_zero_slope_no_crossing
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsFullMomentLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (q θ x a : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
      Integrable (fun ω => Real.exp (θ * D.X 1 ω)) P →
      derivWithin (tiltedScale θ (W q)) (Ici a) a + θ * tiltedScale θ (W q) a = 0 →
      (∫ ω, reflectedSupJointPayoff D.X q θ x a ω ∂P) = 0 := by
  intro Ω mΩ P hP D ψ W hψ hW q θ x a hq ha hx hxa hm hz
  have hrel := (p2m810_source_tilt_derivative Ω P D ψ W hψ.1 hW q a θ hq ha).2
  have hd := (mul_eq_zero.mp (hrel.symm.trans hz)).resolve_left (Real.exp_ne_zero _)
  have hae := p2m810_sup_zero_slope_no_crossing Ω P D ψ W hψ.1 hW
    q x a hq ha hx hxa hd
  calc
    _ = ∫ _ : Ω, (0 : ℝ) ∂P := by
      apply integral_congr_ae
      filter_upwards [hae] with ω hω
      simp [reflectedSupJointPayoff, hω]
    _ = 0 := by simp
