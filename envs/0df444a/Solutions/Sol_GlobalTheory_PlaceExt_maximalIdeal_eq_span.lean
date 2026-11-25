-- Prove2me | solution 1 for GlobalTheory.PlaceExt.maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:32:02.679474+00:00
-- url     : https://prove2.me/submissions/a26e657d-83c3-4183-970a-f66be0c107ab

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
variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
omit [IsLocalHom (algebraMap R R')]
namespace GlobalTheory.PlaceExt
theorem _root_.solution
    (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R' = Ideal.span {algebraMap R R' ϖ} := by
  rw [← hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
    Set.image_singleton]
end GlobalTheory.PlaceExt
