-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_zscale_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:13:57.176817+00:00
-- url     : https://prove2.me/submissions/600997e7-d187-4f56-af4b-8b4d09a50f02


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit reduction. -/
theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W → ∀ q : ℝ, 0 ≤ q →
      ContinuousOn (Zscale q (W q)) (Ici (0 : ℝ)) := by
  intro ψ W hW q hq
  have hc := (hW q hq).2.2.2.1
  let v : ℝ → ℝ := fun t => W q (max t 0)
  have hv : Continuous v := hc.comp_continuous
    (continuous_id.max continuous_const) (fun t => le_max_right t 0)
  have hz : Continuous (fun t => 1 + q * ∫ s in (0 : ℝ)..t, v s) :=
    continuous_const.add (continuous_const.mul
      (intervalIntegral.continuous_primitive (fun a b => hv.intervalIntegrable a b) 0))
  apply hz.continuousOn.congr
  intro t ht
  unfold Zscale
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  simp [v, max_eq_left hs.1]
