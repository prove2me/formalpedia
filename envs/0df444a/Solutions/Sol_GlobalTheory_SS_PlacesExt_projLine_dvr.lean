-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.projLine_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:35:56.708841+00:00
-- url     : https://prove2.me/submissions/049c061f-2b05-4813-8ee2-98686e272ee5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0
variable (k : Type) [Field k]
namespace GlobalTheory.SS.PlacesExt
theorem _root_.solution (i : (projLinePlaces k).I) : IsDiscreteValuationRing ((projLinePlaces k).O i) := by
  classical
  cases i with
  | none =>
    change IsDiscreteValuationRing (RatFunc.inftyValuation k).valuationSubring
    infer_instance
  | some p =>
    change IsDiscreteValuationRing (p.prime.valuation (RatFunc k)).valuationSubring
    infer_instance
end GlobalTheory.SS.PlacesExt
