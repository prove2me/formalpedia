-- Prove2me | solution 1 for GlobalTheory.LOneLower.summable_inv_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:38.694344+00:00
-- url     : https://prove2.me/submissions/976b04da-7633-4ff5-afbc-857495fec2d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower
namespace GlobalTheory.LOneLower
theorem _root_.solution {α : ℝ} (hα : 0 < α) :
    Summable fun d : ℕ => (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ := by
  have h : Summable fun d : ℕ => (2 * (α ^ 2)⁻¹) * (((d + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
    ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).2
      (Real.summable_nat_pow_inv.2 one_lt_two)).mul_left _
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) h
  · have h3 : 0 < ((d + 1 : ℕ) : ℝ) * α := by positivity
    have h4 := Real.add_one_le_exp (((d + 1 : ℕ) : ℝ) * α)
    exact inv_nonneg.2 (by linarith)
  · have h3 : 0 < ((d + 1 : ℕ) : ℝ) * α := by positivity
    have h4 := Real.quadratic_le_exp_of_nonneg h3.le
    have : 2 * (α ^ 2)⁻¹ * (((d + 1 : ℕ) : ℝ) ^ 2)⁻¹ = ((((d + 1 : ℕ) : ℝ) * α) ^ 2 / 2)⁻¹ := by
      field_simp
    rw [this]
    exact inv_anti₀ (by positivity) (by linarith)
end GlobalTheory.LOneLower
