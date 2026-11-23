-- Prove2me | solution 1 for GlobalTheory.SplitWeil.om_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:06.435922+00:00
-- url     : https://prove2.me/submissions/b4d0f0ed-f985-4a40-a8f4-c402d4761776

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one

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
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
namespace GlobalTheory.SplitWeil
theorem _root_.solution (Φ : Matrix b a k → ℂ) : om μ (1 : GL a k) (1 : GL b k) Φ = Φ := by
  funext x
  simp [om, nabs_one]
end GlobalTheory.SplitWeil
