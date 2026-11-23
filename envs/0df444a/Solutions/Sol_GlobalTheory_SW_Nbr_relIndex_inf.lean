-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.relIndex_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:21.727779+00:00
-- url     : https://prove2.me/submissions/031f885c-0344-4519-ae06-23213b0f14c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.Nbr
theorem _root_.solution (Λ Λ' : Lt E n) : (Λ ⊓ Λ').toAddSubgroup.relIndex Λ.toAddSubgroup =
    Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup :=
  AddSubgroup.inf_relIndex_left Λ.toAddSubgroup Λ'.toAddSubgroup
end GlobalTheory.SW.Nbr
