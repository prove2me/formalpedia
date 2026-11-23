-- Prove2me | solution 1 for GlobalTheory.StepData.IntM.mul_maxM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:52.2089+00:00
-- url     : https://prove2.me/submissions/280fd434-1d0c-414c-aba4-0af5c2141154

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
theorem _root_.solution [Fintype m] {M : Matrix l m k} {M' : Matrix m n k} (h : IntM M) (h' : MaxM M') :
    MaxM (M * M') := fun i j => by
  refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_right (h i s) zero_le (h' s j)
end IntM
end GlobalTheory.StepData
