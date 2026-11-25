-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData.charZero_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:18.082111+00:00
-- url     : https://prove2.me/submissions/f8eebbc6-d568-4ca8-b7bc-7e2ddaca523e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PointDataQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt FB)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData
theorem _root_.solution (V : Type) [CommRing V] [IsDomain V] [CharZero V] :
    CharZero (AlgebraicClosure (FractionRing V)) := by
  haveI : CharZero (FractionRing V) := charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  infer_instance
end GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData
