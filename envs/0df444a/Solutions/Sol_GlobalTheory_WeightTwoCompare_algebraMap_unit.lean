-- Prove2me | solution 1 for GlobalTheory.WeightTwoCompare.algebraMap_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:05.051308+00:00
-- url     : https://prove2.me/submissions/f4485864-0a85-49af-98fc-05426e7f12a4

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumDeformedLatticeEisensteinSummandWeightTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.WeightTwoCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.WeightTwoCompare
theorem _root_.solution (u : (OF E)ˣ) :
    algebraMap (OF E) E (u : OF E) = (((u : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E) : E) := rfl
end GlobalTheory.WeightTwoCompare
