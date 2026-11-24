-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.padic_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:06.048344+00:00
-- url     : https://prove2.me/submissions/3c5ab340-2a45-4aea-9826-ca9fd2bab045

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution (p : ℕ) [Fact p.Prime] (x y : ℚ_[p]) :
    valuation ℚ_[p] x < valuation ℚ_[p] y ↔ ‖x‖ < ‖y‖ := by
  rw [(ValuativeRel.isEquiv (valuation ℚ_[p]) (Padic.mulValuation (p := p))).lt_iff_lt]
  by_cases hx : x = 0 <;> by_cases hy : y = 0
  · simp [hx, hy]
  · simp [hx, hy, zero_lt_iff]
  · simp [hx, hy]
  · have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy,
      zpow_lt_zpow_iff_right₀ hp]
    simp [Padic.mulValuation, hx, hy, inv_lt_inv₀]
end GlobalTheory.SplitWeil.Model
