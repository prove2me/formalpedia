-- Prove2me | solution 1 for GlobalTheory.LOneLower.compare_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:41.163009+00:00
-- url     : https://prove2.me/submissions/dc30e92d-891d-4dd9-82f3-b0b95b4d87fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Theorems.Thm_GlobalTheory_LOneLower_abel_bound
import Theorems.Thm_GlobalTheory_LOneLower_char_sum_bound
import Theorems.Thm_GlobalTheory_LOneLower_wt_nonneg
import Theorems.Thm_GlobalTheory_LOneLower_wt_le_one
import Theorems.Thm_GlobalTheory_LOneLower_wt_antitoneOn
import Theorems.Thm_GlobalTheory_LOneLower_summable_inv_exp

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
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) :
    ‖LFunction χ (1 + ε) * ((α⁻¹ : ℝ) : ℂ) - ∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ)‖ ≤ q := by
  have hs : 1 < (1 + (ε : ℂ)).re := by simpa using hε
  have h1 : LSeriesHasSum (χ ·) (1 + ε) (LFunction χ (1 + ε)) := by
    rw [LFunction_eq_LSeries χ hs]
    exact (LSeriesSummable_of_one_lt_re χ hs).LSeriesHasSum
  have h2 := ((hasSum_nat_add_iff' 1).2 h1).mul_right ((α⁻¹ : ℝ) : ℂ)
  simp only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero] at h2
  have hp : ∀ d : ℕ, ((d + 1 : ℕ) : ℝ) ^ (-ε) ≤ 1 := fun d =>
    Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)
  have h3 : Summable fun d : ℕ => χ ((d + 1 : ℕ) : ZMod q) *
      (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ) := by
    refine Summable.of_norm_bounded (summable_inv_exp hα).norm fun d => ?_
    rw [norm_mul, Complex.norm_real, norm_mul]
    refine (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans ?_
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact hp d
  have h4 := h2.sub h3.hasSum
  let b : ℕ → ℝ := fun d => ((d + 1 : ℕ) : ℝ) ^ (-ε) * wt (((d + 1 : ℕ) : ℝ) * α)
  have h5 : ∀ d : ℕ, LSeries.term (χ ·) (1 + ε) (d + 1) * ((α⁻¹ : ℝ) : ℂ)
      - χ ((d + 1 : ℕ) : ZMod q) *
      (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ)
      = χ ((d + 1 : ℕ) : ZMod q) * (b d : ℂ) := by
    intro d
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero d)]
    have : ((d + 1 : ℕ) : ℂ) ^ (1 + (ε : ℂ)) = ((((d + 1 : ℕ) : ℝ) ^ (1 + ε) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity)]
      simp
    rw [this, div_eq_mul_inv, mul_assoc, ← mul_sub, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub]
    congr 2
    simp only [b, wt]
    rw [Real.rpow_add (by positivity), Real.rpow_one, Real.rpow_neg (by positivity)]
    simp only [mul_inv]
    ring
  simp only [h5] at h4
  have hw : ∀ d : ℕ, 0 < ((d + 1 : ℕ) : ℝ) * α := fun d => by positivity
  have hb0 : ∀ d, 0 ≤ b d := fun d => mul_nonneg (by positivity) (wt_nonneg (hw d))
  have hb : Antitone b := by
    intro m n hmn
    have hc : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hmn
    refine mul_le_mul ?_ ?_ (wt_nonneg (hw n)) (by positivity)
    · exact Real.rpow_le_rpow_of_nonpos (by positivity) hc (by linarith)
    · exact wt_antitoneOn (hw m) (hw n) (by gcongr)
  have hb1 : b 0 ≤ 1 := mul_le_one₀ (hp 0) (wt_nonneg (hw 0)) (wt_le_one (hw 0))
  refine le_of_tendsto' h4.tendsto_sum_nat.norm fun N => ?_
  refine (abel_bound _ b q (char_sum_bound χ hχ) hb hb0 N).trans ?_
  exact mul_le_of_le_one_right (by positivity) hb1
end GlobalTheory.LOneLower
