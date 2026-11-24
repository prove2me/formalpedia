-- Prove2me | solution 1 for GlobalTheory.DoublingSeries.ratFun_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:46.065665+00:00
-- url     : https://prove2.me/submissions/c1ec8e18-0f02-4cd6-b96c-6843273b2736

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RatFunDifferentiableOn
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
noncomputable section
open GlobalTheory GlobalTheory.DoublingSeries
namespace GlobalTheory.DoublingSeries
theorem _root_.solution {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (ρ : ℝ)
    (hα : ∀ x, ‖(α x : ℂ)‖ ≤ (q : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (q : ℝ) ^ ρ) :
    DifferentiableOn ℂ (ratFun q N α) (Metric.ball 0 ((q : ℝ) ^ (1 / 2 - ρ))) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have key : ∀ a : ℂ, ‖a‖ ≤ (q : ℝ) ^ ρ → ∀ X ∈ Metric.ball (0 : ℂ) ((q : ℝ) ^ (1 / 2 - ρ)),
      1 - a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X ≠ 0 := by
    intro a ha X hX
    rw [mem_ball_zero_iff] at hX
    have hn : ‖a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X‖ < 1 := by
      rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hre : (-(1 / 2 : ℂ)).re = -(1 / 2) := by norm_num
      rw [hre]
      calc ‖a‖ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * ‖X‖ ≤ (q : ℝ) ^ ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * ‖X‖ := by gcongr
        _ < (q : ℝ) ^ ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (q : ℝ) ^ (1 / 2 - ρ) := by gcongr
        _ = 1 := by rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, show ρ + -(1 / 2 : ℝ) + (1 / 2 - ρ) = 0 by ring, Real.rpow_zero]
    intro h
    have e : a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X = 1 := by linear_combination -h
    rw [e, norm_one] at hn
    exact lt_irrefl _ hn
  unfold ratFun
  refine DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).inv
        fun X hX => key _ (hα i).1 X hX
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).inv
        fun X hX => key (((α i)⁻¹ : ℂˣ) : ℂ) (by rw [Units.val_inv_eq_inv_val, norm_inv]; exact (hα i).2) X hX
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      (differentiableOn_const (𝕜 := ℂ) (1 : ℂ)).sub ((differentiableOn_const (𝕜 := ℂ) ((q : ℂ) ^ (-(i : ℂ)))).mul (differentiableOn_id (𝕜 := ℂ).pow 2))
end GlobalTheory.DoublingSeries
