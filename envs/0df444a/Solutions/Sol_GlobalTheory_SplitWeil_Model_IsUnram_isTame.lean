-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.IsUnram.isTame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:55:59.730795+00:00
-- url     : https://prove2.me/submissions/fab41031-b0ca-4031-9b48-bc2b10d5928a

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
namespace IsUnram
theorem _root_.solution {μ : kˣ →* ℂˣ} (h : IsUnram μ) : IsTame μ := fun x hx =>
  h x (by simpa using (valuation k).map_one_add_of_lt hx)
end IsUnram
end GlobalTheory.SplitWeil.Model
