-- Prove2me | solution 1 for MixFlex.RiskNeutral.correlation_eq_one_affine
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:44:05.914504+00:00
-- url     : https://prove2.me/submissions/919e3549-8060-4fc9-8f75-4ad5a43f73f9

import Definitions.Def_MixFlex_RiskNeutral_Model
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory
open MixFlex.RiskNeutral

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (U V : Ω → ℝ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hvarU : 0 < variance U μ) (hvarV : 0 < variance V μ) (hρ : correlation μ U V = 1) :
    ∃ a b : ℝ, 0 < a ∧ V =ᵐ[μ] fun ω => a * U ω + b := by
  let c := Real.sqrt (variance U μ*variance V μ)
  have hc : 0 < c := Real.sqrt_pos.2 (mul_pos hvarU hvarV)
  have hc2 : c^2=variance U μ*variance V μ := Real.sq_sqrt (by positivity)
  have hcov : covariance U V μ = c := by
    change covariance U V μ / c = 1 at hρ
    exact (div_eq_one_iff_eq hc.ne').mp hρ
  let a := c/variance U μ
  have ha : 0 < a := div_pos hc hvarU
  have hm := hV.sub (hU.const_mul a)
  have hz : variance (fun ω => V ω-a*U ω) μ = 0 := by
    rw [variance_fun_sub hV (hU.const_mul a),covariance_const_mul_right,
      covariance_comm V U, hcov, variance_const_mul]
    dsimp [a]
    field_simp [hvarU.ne']
    nlinarith [hc2]
  refine ⟨a, ∫ ω, V ω-a*U ω ∂μ, ha, ?_⟩
  filter_upwards [ae_eq_integral_of_variance_eq_zero hm hz] with ω hω
  change V ω-a*U ω = (∫ x, V x-a*U x ∂μ) at hω
  linarith
