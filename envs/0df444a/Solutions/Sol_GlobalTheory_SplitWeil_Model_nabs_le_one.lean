-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.nabs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:09:40.414051+00:00
-- url     : https://prove2.me/submissions/85fc9cf8-4ab3-4b87-a167-46f40311a030

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_SplitWeil_Model_exists_isUnitVol
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_vol

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
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution (x : kˣ) (hx : valuation k (x : k) ≤ 1) : nabs k x ≤ 1 := by
  obtain ⟨ν, h⟩ := exists_isUnitVol (k := k)
  have : ν (x • (𝒪[k] : Set k)) ≤ ν (𝒪[k] : Set k) := by
    apply measure_mono
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (show (x : k) ∈ 𝒪[k] from hx) hy
  rw [nabs_vol ν h, h.2] at this
  exact ENNReal.ofReal_le_one.1 this
end GlobalTheory.SplitWeil.Model
