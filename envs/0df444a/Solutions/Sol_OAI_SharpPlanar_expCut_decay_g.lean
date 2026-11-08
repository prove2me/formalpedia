-- Prove2me | solution 1 for OAI.SharpPlanar.expCut_decay_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:07:41.70793+00:00
-- url     : https://prove2.me/submissions/4fe95453-8790-4757-88be-21b8c1a48f52

import Mathlib
import Definitions.Def_OAIQ098G012
import Theorems.Thm_OAI_SharpPlanar_expCut_smooth_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

namespace SharpPlanar

lemma expCut_eq (c x : ℝ) (hx : 0 ≤ x) : expCut c x = Real.exp (-c*x) := by
  simp [expCut, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x+1)]

lemma expCut_zero (c x : ℝ) (hx : x ≤ -1) : expCut c x = 0 := by
  simp [expCut, Real.smoothTransition.zero_of_nonpos (by linarith : x+1 ≤ 0)]

lemma iteratedDeriv_expCut_pos (c : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (expCut c) x = (-c)^n * Real.exp (-c*x) := by
  have he : expCut c =ᶠ[𝓝 x] (fun y => Real.exp (-c*y)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact expCut_eq c y hy.le
  rw [he.iteratedDeriv_eq n, iteratedDeriv_exp_const_mul]

lemma iteratedDeriv_expCut_neg (c : ℝ) (n : ℕ) {x : ℝ} (hx : x < -1) :
    iteratedDeriv n (expCut c) x = 0 := by
  have he : expCut c =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact expCut_zero c y hy.le
  rw [he.iteratedDeriv_eq n]
  simp

lemma expCut_decay_g_oai (c : ℝ) (hc : 0 < c) (k n : ℕ) :
    ∃ C : ℝ, ∀ x, ‖x‖^k * ‖iteratedFDeriv ℝ n (expCut c) x‖ ≤ C := by
  let g : ℝ → ℝ := fun x => ‖x‖^k * ‖iteratedDeriv n (expCut c) x‖
  have hg : Continuous g := by
    exact (continuous_norm.pow k).mul
      (((expCut_smooth_g c).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).norm)
  have ht : Tendsto g atTop (𝓝 0) := by
    have he : g =ᶠ[atTop] (fun x : ℝ => (x^(k : ℝ) * Real.exp (-c*x)) * ‖(-c)^n‖) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      change ‖x‖^k * ‖iteratedDeriv n (expCut c) x‖ = _
      rw [iteratedDeriv_expCut_pos c n hx, norm_mul]
      simp only [Real.norm_eq_abs, abs_of_pos hx, Real.rpow_natCast, Real.abs_exp]
      ring
    apply Tendsto.congr' he.symm
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).mul_const ‖(-c)^n‖
  have hb : Tendsto g atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
    simp [g, iteratedDeriv_expCut_neg c n hx]
  have hbd := hg.isBounded_range_iff_isBigO_atTop_atBot.mpr
    ⟨ht.isBigO_one ℝ, hb.isBigO_one ℝ⟩
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  refine ⟨C, fun x => ?_⟩
  have hx := hC (g x) (mem_range_self x)
  simpa only [g, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, norm_norm] using hx

end SharpPlanar


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.expCut_decay_g_oai := @OAI.SharpPlanar.expCut_decay_g_oai
