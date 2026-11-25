-- Prove2me | solution 1 for GlobalTheory.normDiscrete_mem_vRing_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:21:41.333869+00:00
-- url     : https://prove2.me/submissions/6174f3cc-3d81-463c-b499-3cf80a41c820

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_ExistsCompleteDiscreteValuationRingOfIsNormDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct
open GlobalTheory
variable {Ω : Type*} [Field Ω] {v : AddValuation Ω (WithTop ℤ)}
namespace GlobalTheory
theorem _root_.solution (x : Ω) : x ∈ vRing v ↔ 0 ≤ v x := Iff.rfl
end GlobalTheory
