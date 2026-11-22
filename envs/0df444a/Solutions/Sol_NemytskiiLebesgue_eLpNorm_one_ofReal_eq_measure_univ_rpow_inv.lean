-- Prove2me | solution 1 for NemytskiiLebesgue.eLpNorm_one_ofReal_eq_measure_univ_rpow_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:28.900018+00:00
-- url     : https://prove2.me/submissions/66a785f4-51e6-408d-90bf-7602e2eea99f

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p α : ℝ} (hp : 0 < p) (hα : 0 < α) :
    eLpNorm ↓(1 : ℝ) ↱(p / α) μ = (μ ⊤) ^ (α / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal] <;> norm_num [hp, hα, div_eq_mul_inv,
    aestronglyMeasurable_const]
  rw [ENNReal.toReal_ofReal (by positivity), inv_eq_one_div, div_eq_mul_inv]
  norm_num [mul_comm]
end NemytskiiLebesgue
