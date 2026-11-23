-- Prove2me | solution 1 for GlobalTheory.SS.Slope.exists_min
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:12.200818+00:00
-- url     : https://prove2.me/submissions/c31ed179-8b04-447e-b45e-1d4e06190a64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightedOrderSlopeComparison

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Slope
open MvPowerSeries
variable {k : Type} [Field k]
namespace GlobalTheory.SS.Slope
theorem _root_.solution (w : Fin 2 → ℕ) (f : MvPowerSeries (Fin 2) k) (hf : f ≠ 0) :
    ∃ s, coeff s f ≠ 0 ∧ (Finsupp.weight w s : ℕ∞) = weightedOrder w f :=
  exists_coeff_ne_zero_and_weightedOrder w ((ne_zero_iff_weightedOrder_finite w).1 hf)
end GlobalTheory.SS.Slope
