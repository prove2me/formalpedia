-- Prove2me | solution 1 for GlobalTheory.normDiscrete_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:27:01.749405+00:00
-- url     : https://prove2.me/submissions/5193b1d0-12af-4b31-8e40-3c45ae90674d

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
theorem _root_.solution {x : Ω} {n : ℤ} (hx : v x = (n : WithTop ℤ)) :
    v x⁻¹ = ((-n : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_inv, hx]
  rfl
end GlobalTheory
