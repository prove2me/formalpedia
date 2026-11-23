-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplZeta.LeftShift.rpow_le_exp_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:52.451425+00:00
-- url     : https://prove2.me/submissions/d71ba9af-e182-407c-bfee-6332d8fde3f8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplZeta GlobalTheory.CompanionTheory.ExplZeta.LeftShift
namespace GlobalTheory.CompanionTheory.ExplZeta.LeftShift
theorem _root_.solution {x σ : ℝ} (hx : 2 ≤ x) (hσ : σ ≤ 0) :
    x ^ σ ≤ Real.exp (σ / 2) := by
  have h1 : x ^ σ ≤ (2 : ℝ) ^ σ := Real.rpow_le_rpow_of_nonpos (by norm_num) hx hσ
  have h2 : (2 : ℝ) ^ σ = Real.exp (Real.log 2 * σ) := Real.rpow_def_of_pos (by norm_num) σ
  have h3 : Real.log 2 * σ ≤ σ / 2 := by
    have := Real.log_two_gt_d9
    nlinarith
  calc x ^ σ ≤ (2 : ℝ) ^ σ := h1
    _ = Real.exp (Real.log 2 * σ) := h2
    _ ≤ Real.exp (σ / 2) := Real.exp_le_exp.mpr h3
end GlobalTheory.CompanionTheory.ExplZeta.LeftShift
