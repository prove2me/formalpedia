-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_overshoot_payoff_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:01:39.795495+00:00
-- url     : https://prove2.me/submissions/000fc6a1-105b-47c5-a776-d80c115c0714
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_derivative_exact
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_7_ii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_esscher_coefficient_at_root
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_shifted_overshoot_payoff_eq
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (y : ℝ) (hy : 0 < y) :
    deriv (Phi ψ) q * (∫ ω, downOvershootTilt D.X q (Phi ψ q) y ω ∂P) =
      deriv (Phi ψ) q * Real.exp (Phi ψ q * y) - W q y := by
  have hr := (hW q hq.le).1.2.1
  have hroot : ψ (Phi ψ q) = q := hr.2
  obtain ⟨hp, hi⟩ := p2m89_phi_derivative_exact D ψ W hψ hW q hq
  have hess := (part_exercise8_7_ii_v2 Ω P D ψ W hψ hW y (Phi ψ q) q hy hr.1 hq.le).1
  have hcoeff := p2m810_esscher_coefficient_at_root D ψ W hψ hW q hq
  simp only [hroot, sub_self, Zscale, zero_mul, add_zero, hcoeff, tiltedScale] at hess
  rw [p2m810_shifted_overshoot_payoff_eq, hess, hi, neg_mul, Real.exp_neg]
  field_simp [hp.ne', Real.exp_ne_zero _]
  <;> ring
