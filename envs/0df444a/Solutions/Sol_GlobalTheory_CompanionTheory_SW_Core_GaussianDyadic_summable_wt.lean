-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.summable_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:17:28.453797+00:00
-- url     : https://prove2.me/submissions/84f8f88a-7b54-402c-a528-4f1ba127e33f

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_wt_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
theorem _root_.solution {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j := by
  set K : ℝ := ((n + 1).factorial : ℝ) * (4 / c) ^ (n + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hgeo : Summable fun j : ℕ => (K + 1) * ((1 : ℝ) / 4) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (wt_nonneg c j) (by positivity)) ?_ hgeo
  intro j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [wt]; linarith
  · have hj0 : j ≠ 0 := by omega
    simp only [wt, hj0, if_false]
    set y : ℝ := 4 ^ j with hy
    have hy0 : 0 < y := by positivity
    have hx0 : 0 ≤ c * y / 4 := by positivity
    have hb := Real.pow_div_factorial_le_exp (c * y / 4) hx0 (n + 1)
    have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    have hxp : 0 < (c * y / 4) ^ (n + 1) := by positivity
    have hexp : Real.exp (-(c * y / 4)) ≤ ((n + 1).factorial : ℝ) / (c * y / 4) ^ (n + 1) := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      exact hb
    have hswap : ((4 : ℝ) ^ n) ^ j = y ^ n := by rw [hy, ← pow_mul, ← pow_mul, mul_comm]
    rw [hswap]
    calc Real.exp (-(c * y / 4)) * y ^ n
        ≤ ((n + 1).factorial : ℝ) / (c * y / 4) ^ (n + 1) * y ^ n :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = K * (1 / 4) ^ j := by
          have : ((1 : ℝ) / 4) ^ j = y⁻¹ := by rw [hy, one_div, inv_pow]
          rw [this, hK, div_pow, div_pow, mul_pow, pow_succ y n]
          field_simp
      _ ≤ (K + 1) * (1 / 4) ^ j := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
