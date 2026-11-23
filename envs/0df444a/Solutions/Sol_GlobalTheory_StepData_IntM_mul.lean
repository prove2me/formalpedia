-- Prove2me | solution 1 for GlobalTheory.StepData.IntM.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:35.073574+00:00
-- url     : https://prove2.me/submissions/05baa754-4b26-4c6f-a368-6a39f1061618

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
theorem _root_.solution [Fintype m] {M : Matrix l m k} {M' : Matrix m n k} (h : IntM M) (h' : IntM M') :
    IntM (M * M') := fun i j => sum_mem fun s _ => mul_mem (h i s) (h' s j)
end IntM
end GlobalTheory.StepData
