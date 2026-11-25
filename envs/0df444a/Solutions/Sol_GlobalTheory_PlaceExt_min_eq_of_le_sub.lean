-- Prove2me | solution 1 for GlobalTheory.PlaceExt.min_eq_of_le_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:24:58.226543+00:00
-- url     : https://prove2.me/submissions/871bfd10-b27a-4ea0-bd14-8c75142fcf9b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.PlaceExt
variable {L A : Type*} [Field L] [CommRing A]
namespace GlobalTheory.PlaceExt
theorem _root_.solution (u : AddValuation A (WithTop ℤ)) {x y : A} {M : WithTop ℤ}
    (h : M ≤ u (x - y)) : min (u x) M = min (u y) M := by
  have h1 : min (u (x - y)) (u y) ≤ u x := by simpa using u.map_add (x - y) y
  have h2 : min (u (x - y)) (u x) ≤ u y := by
    have := u.map_add (y - x) x
    rw [u.map_sub_swap y x] at this
    simpa using this
  grind
end GlobalTheory.PlaceExt
