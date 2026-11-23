-- Prove2me | solution 1 for GlobalTheory.SS.StalkGlue.germ_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:13.117863+00:00
-- url     : https://prove2.me/submissions/38dc7132-ebba-4ee4-bab9-fdfe6b4fc9dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsVf

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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StalkGlue
namespace GlobalTheory.SS.StalkGlue
theorem _root_.solution {X : Scheme.{0}} {U V : X.Opens} (i : V ⟶ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom ((X.presheaf.map i.op).hom s) =
      (X.presheaf.germ U x (i.le hx)).hom s :=
  TopCat.Presheaf.germ_res_apply X.presheaf i x hx s
end GlobalTheory.SS.StalkGlue
