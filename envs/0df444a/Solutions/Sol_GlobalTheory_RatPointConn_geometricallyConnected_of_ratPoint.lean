-- Prove2me | solution 1 for GlobalTheory.RatPointConn.geometricallyConnected_of_ratPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:17:58.075104+00:00
-- url     : https://prove2.me/submissions/37302fcf-ba34-4f61-b27a-393980a1dbbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfRatPoint
import Theorems.Thm_GlobalTheory_RatPointConn_of_section

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
open GlobalTheory GlobalTheory.RatPointConn
universe u
namespace GlobalTheory.RatPointConn
theorem _root_.solution :
    ∀ (k : Type) [Field k] (X : Over (Sp k)), LocallyOfFiniteType X.hom → QuasiCompact X.hom → ConnectedSpace X.left → Nonempty (𝟙_ (Over (Sp k)) ⟶ X) → GeometricallyConnected X.hom := by
  rintro k _ X _ - _ ⟨s⟩
  exact of_section (k := k) X.hom s.left (Over.w s)
end GlobalTheory.RatPointConn
