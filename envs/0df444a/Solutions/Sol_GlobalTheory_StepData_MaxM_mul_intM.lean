-- Prove2me | solution 1 for GlobalTheory.StepData.MaxM.mul_intM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:52.273724+00:00
-- url     : https://prove2.me/submissions/7b73c074-7af7-44e2-b74d-c64b4a198736

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
namespace MaxM
theorem _root_.solution [Fintype m] {M : Matrix l m k} {M' : Matrix m n k} (h : MaxM M) (h' : IntM M') :
    MaxM (M * M') := fun i j => by
  refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (h i s) (h' s j)
end MaxM
end GlobalTheory.StepData
