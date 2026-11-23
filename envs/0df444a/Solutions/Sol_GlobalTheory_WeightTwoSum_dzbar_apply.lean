-- Prove2me | solution 1 for GlobalTheory.WeightTwoSum.dzbar_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:01.714832+00:00
-- url     : https://prove2.me/submissions/e5307e18-36d5-46a8-b394-fb115602237e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff
open GlobalTheory GlobalTheory.WeightTwoSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.WeightTwoSum
theorem _root_.solution (j : I) (v : I → ℂ) : dzbar j v = starRingEnd ℂ (v j) := rfl
end GlobalTheory.WeightTwoSum
