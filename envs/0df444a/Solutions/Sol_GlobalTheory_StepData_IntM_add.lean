-- Prove2me | solution 1 for GlobalTheory.StepData.IntM.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:36.359806+00:00
-- url     : https://prove2.me/submissions/e3519fac-3275-4a46-81ba-6dc03d754195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable {l m n : Type*}
namespace GlobalTheory.StepData
namespace IntM
theorem _root_.solution {M M' : Matrix m n k} (h : IntM M) (h' : IntM M') : IntM (M + M') :=
  fun i j => add_mem (h i j) (h' i j)
end IntM
end GlobalTheory.StepData
