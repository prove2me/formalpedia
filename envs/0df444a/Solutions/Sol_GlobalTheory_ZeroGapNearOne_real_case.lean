-- Prove2me | solution 1 for GlobalTheory.ZeroGapNearOne.real_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:49.964734+00:00
-- url     : https://prove2.me/submissions/bc3be27e-e69d-42b7-9d12-d8d3cefe2918

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsNormDerivLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOne
import Theorems.Thm_GlobalTheory_ZeroGapNearOne_log_pos
import Theorems.Thm_GlobalTheory_ZeroGapNearOne_log_le_sqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.ZeroGapNearOne
namespace GlobalTheory.ZeroGapNearOne
theorem _root_.solution {x a C c δ : ℝ} (hx : 1 ≤ x) (hC : 0 < C) (hδ : 0 ≤ δ) (hc : 0 < c)
    (hca : c ≤ a / (4 * C))
    (h : a / x ^ ((3 : ℝ) / 2) ≤ C * Real.log (3 * x) ^ 2 * δ) :
    c / (x ^ 2 * Real.log (3 * x)) ≤ δ := by
  have hL := log_pos hx
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hsq : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have hx0 : 0 < x := by linarith
  have hp : x ^ ((3 : ℝ) / 2) = x * √x := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx0,
      Real.rpow_one]
  rw [hp, div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)] at hca
  rw [div_le_iff₀ (by positivity)]
  have hl := log_le_sqrt hx
  have h3 : C * Real.log (3 * x) ^ 2 * δ * (x * √x)
      ≤ (C * Real.log (3 * x) * δ * (x * √x)) * (4 * √x) := by
    calc _ = (C * Real.log (3 * x) * δ * (x * √x)) * Real.log (3 * x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  have h4 : (C * Real.log (3 * x) * δ * (x * √x)) * (4 * √x)
      = δ * (x ^ 2 * Real.log (3 * x)) * (4 * C) := by
    calc _ = 4 * C * Real.log (3 * x) * δ * x * (√x * √x) := by ring
      _ = _ := by rw [hsq]; ring
  have h5 : c * (4 * C) ≤ δ * (x ^ 2 * Real.log (3 * x)) * (4 * C) := by linarith
  exact le_of_mul_le_mul_right h5 (by positivity)
end GlobalTheory.ZeroGapNearOne
