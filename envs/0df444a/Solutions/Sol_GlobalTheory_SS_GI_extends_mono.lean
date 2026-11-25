-- Prove2me | solution 1 for GlobalTheory.SS.GI.extends_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:13:38.199356+00:00
-- url     : https://prove2.me/submissions/4a5e7ad7-25a0-4402-9926-6bd5178db7c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_extends_iff_via

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
theorem _root_.solution {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U V : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) (hV : V ≤ U) :
    Extends M N f V (M.Y.left.homOfLE hV ≫ g) :=
  extends_iff_via.2 (by simpa using (extends_iff_via.1 h).precomp (M.Y.left.homOfLE hV))
end GlobalTheory.SS.GI
