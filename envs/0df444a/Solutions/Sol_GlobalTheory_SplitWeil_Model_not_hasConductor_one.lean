-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.not_hasConductor_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:14:49.210004+00:00
-- url     : https://prove2.me/submissions/f9d49b83-c6f3-433d-9ce8-16abc9d7b01e

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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution (c : kˣ) : ¬ HasConductor (1 : AddChar k Circle) c := by
  intro h
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have := (h (c / r)).1 (fun y _ => rfl)
  have hc : valuation k (c : k) ≠ 0 := by simp
  have hr' : valuation k r ≠ 0 := by simpa using hr
  rw [map_div₀, div_le_iff₀ (zero_lt_iff.2 hr')] at this
  have h2 : valuation k (c : k) * valuation k r < valuation k (c : k) * 1 :=
    mul_lt_mul_of_pos_left hr1 (zero_lt_iff.2 hc)
  rw [mul_one] at h2
  exact absurd this (not_le.2 h2)
end GlobalTheory.SplitWeil.Model
