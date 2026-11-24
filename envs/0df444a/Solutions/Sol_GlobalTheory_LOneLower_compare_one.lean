-- Prove2me | solution 1 for GlobalTheory.LOneLower.compare_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:34.290489+00:00
-- url     : https://prove2.me/submissions/360928fc-6ef5-45c9-8d87-186971107649

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Theorems.Thm_GlobalTheory_LOneLower_summable_inv_exp
import Theorems.Thm_GlobalTheory_LOneLower_compare_right

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
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {α : ℝ}
    (hα : 0 < α) :
    ‖LFunction χ 1 * ((α⁻¹ : ℝ) : ℂ) - ∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ) : ℂ)‖ ≤ q := by
  have h1 : Tendsto (fun ε : ℝ => LFunction χ (1 + ε)) (𝓝[>] 0) (𝓝 (LFunction χ 1)) := by
    have : Continuous fun ε : ℝ => LFunction χ (1 + ε) :=
      (differentiable_LFunction hχ).continuous.comp (by fun_prop)
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ => ∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ))
      (𝓝[>] 0) (𝓝 (∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ) : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence (summable_inv_exp hα).norm (fun d => ?_) ?_
    · have hc : Continuous fun ε : ℝ => ((d + 1 : ℕ) : ℝ) ^ (-ε) :=
        (Real.continuous_const_rpow (by positivity)).comp continuous_neg
      have : Continuous fun ε : ℝ => χ ((d + 1 : ℕ) : ZMod q) *
        (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ) :=
        continuous_const.mul (Complex.continuous_ofReal.comp (hc.mul continuous_const))
      have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [neg_zero, Real.rpow_zero, one_mul] at this
    · filter_upwards [self_mem_nhdsWithin] with ε hε d
      have hε' : 0 < ε := hε
      rw [norm_mul, Complex.norm_real, norm_mul]
      refine (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans ?_
      refine mul_le_of_le_one_left (by positivity) ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)
  refine le_of_tendsto ((h1.mul_const _).sub h2).norm ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact compare_right χ hχ hα hε
end GlobalTheory.LOneLower
