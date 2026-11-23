-- Prove2me | solution 1 for GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:28.837395+00:00
-- url     : https://prove2.me/submissions/dfcc1b18-c81e-4329-8a79-fbcf72e67180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_exists_isUnitVol
import Theorems.Thm_GlobalTheory_SplitWeil_measureReal_cball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
namespace GlobalTheory.SplitWeil
theorem _root_.solution {x : kˣ} (hx : valuation k (x : k) = 1) : nabs k x = 1 := by
  borelize k
  obtain ⟨ν, hν, h1⟩ := exists_isUnitVol k
  have h := measureReal_cball ν x
  have : cball x = (𝒪[k] : Set k) := by
    ext y; simp [cball, hx, Valuation.mem_integer_iff]
  rw [this, Measure.real, h1] at h
  simpa using h.symm
end GlobalTheory.SplitWeil
