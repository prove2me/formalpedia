-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.padic_valTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:56:01.965399+00:00
-- url     : https://prove2.me/submissions/ee6bd3a9-d415-45fb-93a6-530dafa7e6c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_SplitWeil_Model_padic_lt

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] : IsValuativeTopology ℚ_[p] := by
  refine IsValuativeTopology.of_zero fun s => ?_
  rw [Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, hs⟩
    obtain ⟨y, hy0, hy⟩ := NormedField.exists_norm_lt ℚ_[p] hε
    have hy' : y ≠ 0 := norm_pos_iff.1 hy0
    refine ⟨Units.mk0 (valuation ℚ_[p] y) (by simpa using hy'), fun z hz => hs ?_⟩
    have : ‖z‖ < ‖y‖ := (padic_lt p z y).1 hz
    simpa using this.trans hy
  · rintro ⟨γ, hγ⟩
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero ℚ_[p])
    have hy' : y ≠ 0 := by rintro rfl; exact γ.ne_zero (by simpa using hy.symm)
    refine ⟨‖y‖, norm_pos_iff.2 hy', fun z hz => hγ ?_⟩
    show valuation ℚ_[p] z < γ
    rw [← hy, padic_lt]; simpa using hz
end GlobalTheory.SplitWeil.Model
