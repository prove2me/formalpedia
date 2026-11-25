-- Prove2me | solution 1 for GlobalTheory.SS.GI.extends_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:13.144799+00:00
-- url     : https://prove2.me/submissions/eee30689-da58-409d-b74d-20de7e8cd372

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_extends_iff_via
import Theorems.Thm_GlobalTheory_SS_GI_Via_unique

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GI
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' B B' : Over (Sp K)}
namespace GlobalTheory.SS.GI
theorem _root_.solution [IsDomain R] [IsFractionRing R K] {M : Model R A} {N : Model R A'} {f : A ⟶ A'}
    {U : M.Y.left.Opens} {g g' : U.toScheme ⟶ N.Y.left}
    (h : Extends M N f U g) (h' : Extends M N f U g') : g = g' :=
  (extends_iff_via.1 h).unique (extends_iff_via.1 h')
end GlobalTheory.SS.GI
